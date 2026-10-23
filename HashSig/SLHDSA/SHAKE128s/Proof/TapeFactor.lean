/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.DigestTape
public import HashSig.SLHDSA.SHAKE128s.Proof.SplitPrefix
public import HashSig.SLHDSA.SHAKE128s.Proof.RecorderView

/-!
# The recording, read off a tape drawn in advance

A union bound over the words a recorded event is witnessed by loses the per-run weight the
coverage charge needs: it is compatible with a run whose whole mass sits on bad words of one
length. What it throws away is the conditional uniformity of the recording *given its length*.

This file keeps it, by drawing the tape first. `tapeRecorder` is the recording oracle with its
fresh class answers taken off a list fixed in advance instead of drawn on the spot, falling back
to a draw when the list is spent, so no length hypothesis is needed anywhere. `splitTapeRecorder`
is the two-block form, with one block for the disclosing answers and one for the target answers.

Only the class answers have to come off a tape: the coins and the out-of-class answers may stay
inline, because the selection has to be *causal*, not deterministic. The file holds the two
recorders, their step laws, the lemmas that move a block past an irrelevant draw and overwrite
one cell of a block, and the correspondence between recorded entries and block cells.
`NoticingTape` runs the induction over a computation at the noticing recorder.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.TapeFactor

open DigestTape

/-- The cache, the unread remainder of the tape, and the recording so far. -/
abbrev TapeState := QueryCache HashSpec × List HashOutput × Record

open scoped Classical in
/-- **The recording oracle with its class answers read off a tape.** A fresh query whose input
passes `keep` takes the head of the tape as its answer; everything else draws as before, and so
does a class query made after the tape is spent. -/
noncomputable def tapeRecorder (keep : Bytes → Prop) :
    QueryImpl OracleWorld (StateT TapeState ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input =>
        if keep input ∧ state.1 input = none then
          match state.2.1 with
          | head :: rest =>
              (pure (head, (state.1.cacheQuery input head, rest,
                state.2.2 ++ [(input, head)])) : ProbComp _)
          | [] => do
              let value ← ($ᵗ HashOutput : ProbComp HashOutput)
              pure (value, (state.1.cacheQuery input value, ([] : List HashOutput),
                state.2.2 ++ [(input, value)]))
        else do
          let step ← (randomOracle input).run state.1
          pure (step.1, (step.2, state.2.1, state.2.2))

/-! ## Normalising a block at the head of a bind

Both factorisations read their blocks head-first, so the two shapes a block takes under a bind
are worth having as rewrites that go under a binder: a spent block disappears, and a block with
one more answer splits into that answer and the rest. -/

theorem padding_zero_bind {γ : Type} (continuation : List HashOutput → ProbComp γ) :
    padding 0 >>= continuation = continuation [] := by
  rw [padding]
  simp only [pure_bind]

theorem padding_succ_bind {γ : Type} (length : Nat)
    (continuation : List HashOutput → ProbComp γ) :
    padding (length + 1) >>= continuation =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        padding length >>= fun rest => continuation (value :: rest) := by
  rw [padding]
  simp only [bind_assoc, pure_bind]

/-! ## Two blocks, one for each role

The coverage charge needs the disclosing answers and the target answers on *separately drawn*
blocks, because the resampling it runs on overwrites one target coordinate and requires the
disclosure set not to move. With one block the two roles interleave at run-dependent positions
and nothing is fixed; with two, the disclosures are a function of a block the overwrite does not
touch.

The induction is the one above with its drawing case split in two. Each block splices its own
head, and whichever block is not being read commutes past the step like any other
answer-irrelevant draw. -/

variable {σ : Type} [RecorderView.CacheView σ]

/-- The view's carrier, the unread remainders of the two blocks, and the two recordings. -/
abbrev SplitTapeState (σ : Type) :=
  σ × (List HashOutput × List HashOutput) × (Record × Record)

open scoped Classical in
/-- **A query neither block answers**, as the shared oracle does it: a hit returns the cached
answer and leaves the carrier, a miss draws and installs. Naming it keeps the "neither" branch
a single equation at a general view, which is what lets every proof below treat that branch as
one opaque step exactly as it did at the cache. -/
noncomputable def plainStep (input : Bytes) (state : σ) : ProbComp (HashOutput × σ) :=
  match RecorderView.CacheView.cacheOf state input with
  | some cached => (pure (cached, state) : ProbComp _)
  | none =>
      (fun answer => (answer, RecorderView.CacheView.update state input answer)) <$>
        ($ᵗ HashOutput : ProbComp _)

open scoped Classical in
/-- **The drawing recorder's own "neither" branch**, in the same single-equation shape. -/
theorem recorderOf_run_inr_plain (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (cache : σ) (records : Record × Record)
    (hskip : ¬ (RecorderView.CacheView.cacheOf cache input = none ∧ leftKeep input cache))
    (hskip' : ¬ (RecorderView.CacheView.cacheOf cache input = none ∧ rightKeep input cache)) :
    ((RecorderView.recorderOf leftKeep rightKeep) (Sum.inr input)).run (cache, records) =
      plainStep input cache >>= fun step =>
        (pure (step.1, (step.2, records)) : ProbComp _) := by
  classical
  cases hcached : RecorderView.CacheView.cacheOf cache input with
  | some cached =>
    rw [RecorderView.recorderOf_run_inr_some _ _ input (cache, records) cached hcached,
      RecorderView.appendedOf_of_cached _ _ input (cache, records) cached cached hcached,
      plainStep]
    rw [hcached]
    simp
  | none =>
    rw [RecorderView.recorderOf_run_inr_none _ _ input (cache, records) hcached, plainStep]
    rw [hcached]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine congrArg (fun step => ($ᵗ HashOutput : ProbComp HashOutput) >>= step) ?_
    funext value
    rw [RecorderView.appendedOf_of_neither _ _ input (cache, records) value
      (fun hleft => hskip ⟨hcached, hleft⟩) (fun hright => hskip' ⟨hcached, hright⟩)]

open scoped Classical in
/-- **The two-recording oracle with each role's answers read off its own block.** The left test
is tried first, so one answer is never read off both blocks. -/
noncomputable def splitTapeRecorder
    (leftKeep rightKeep : Bytes → σ → Prop) :
    QueryImpl OracleWorld (StateT (SplitTapeState σ) ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input =>
        if RecorderView.CacheView.cacheOf state.1 input = none ∧ leftKeep input state.1 then
          match state.2.1.1 with
          | head :: rest =>
              (pure (head, (RecorderView.CacheView.update state.1 input head, (rest, state.2.1.2),
                (state.2.2.1 ++ [(input, head)], state.2.2.2))) : ProbComp _)
          | [] => do
              let value ← ($ᵗ HashOutput : ProbComp HashOutput)
              pure (value, (RecorderView.CacheView.update state.1 input value,
                (([] : List HashOutput), state.2.1.2),
                (state.2.2.1 ++ [(input, value)], state.2.2.2)))
        else if RecorderView.CacheView.cacheOf state.1 input = none ∧ rightKeep input state.1 then
          match state.2.1.2 with
          | head :: rest =>
              (pure (head, (RecorderView.CacheView.update state.1 input head, (state.2.1.1, rest),
                (state.2.2.1, state.2.2.2 ++ [(input, head)]))) : ProbComp _)
          | [] => do
              let value ← ($ᵗ HashOutput : ProbComp HashOutput)
              pure (value, (RecorderView.CacheView.update state.1 input value,
                (state.2.1.1, ([] : List HashOutput)),
                (state.2.2.1, state.2.2.2 ++ [(input, value)])))
        else do
          let step ← plainStep input state.1
          pure (step.1, (step.2, state.2.1, state.2.2))

/-! ### The step shapes -/

open scoped Classical in
theorem splitTapeRecorder_run_inl
    (leftKeep rightKeep : Bytes → σ → Prop) (coin : unifSpec.Domain)
    (state : SplitTapeState σ) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inl coin)).run state =
      ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) >>= fun value =>
        (pure (value, state) : ProbComp _) := rfl

open scoped Classical in
theorem splitTapeRecorder_run_left_cons
    (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (cache : σ) (head : HashOutput) (rest rightTape : List HashOutput)
    (leftRecord rightRecord : Record)
    (hfresh : RecorderView.CacheView.cacheOf cache input = none) (hleft : leftKeep input cache) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, (head :: rest, rightTape), (leftRecord, rightRecord)) =
      (pure (head, (RecorderView.CacheView.update cache input head, (rest, rightTape),
        (leftRecord ++ [(input, head)], rightRecord))) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_pos ⟨hfresh, hleft⟩]

open scoped Classical in
theorem splitTapeRecorder_run_left_nil
    (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (cache : σ) (rightTape : List HashOutput)
    (leftRecord rightRecord : Record)
    (hfresh : RecorderView.CacheView.cacheOf cache input = none) (hleft : leftKeep input cache) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, ([], rightTape), (leftRecord, rightRecord)) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (RecorderView.CacheView.update cache input value, (([] : List HashOutput), rightTape),
          (leftRecord ++ [(input, value)], rightRecord))) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_pos ⟨hfresh, hleft⟩]

open scoped Classical in
theorem splitTapeRecorder_run_right_cons
    (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (cache : σ) (leftTape : List HashOutput) (head : HashOutput)
    (rest : List HashOutput) (leftRecord rightRecord : Record)
    (hfresh : RecorderView.CacheView.cacheOf cache input = none) (hleft : ¬ leftKeep input cache)
    (hright : rightKeep input cache) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, (leftTape, head :: rest), (leftRecord, rightRecord)) =
      (pure (head, (RecorderView.CacheView.update cache input head, (leftTape, rest),
        (leftRecord, rightRecord ++ [(input, head)]))) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_neg (fun h => hleft h.2), if_pos ⟨hfresh, hright⟩]

open scoped Classical in
theorem splitTapeRecorder_run_right_nil
    (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (cache : σ) (leftTape : List HashOutput)
    (leftRecord rightRecord : Record)
    (hfresh : RecorderView.CacheView.cacheOf cache input = none) (hleft : ¬ leftKeep input cache)
    (hright : rightKeep input cache) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (cache, (leftTape, []), (leftRecord, rightRecord)) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (RecorderView.CacheView.update cache input value, (leftTape, ([] : List HashOutput)),
          (leftRecord, rightRecord ++ [(input, value)]))) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_neg (fun h => hleft h.2), if_pos ⟨hfresh, hright⟩]

open scoped Classical in
theorem splitTapeRecorder_run_other
    (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (cache : σ) (tapes : List HashOutput × List HashOutput)
    (records : Record × Record)
    (hskip : ¬ (RecorderView.CacheView.cacheOf cache input = none ∧ leftKeep input cache))
    (hskip' : ¬ (RecorderView.CacheView.cacheOf cache input = none ∧ rightKeep input cache)) :
    ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run (cache, tapes, records) =
      plainStep input cache >>= fun step =>
        (pure (step.1, (step.2, tapes, records)) : ProbComp _) := by
  classical
  simp only [splitTapeRecorder, StateT.run]
  rw [if_neg hskip, if_neg hskip']

/-! ### The same shapes for the drawing recorder -/

open scoped Classical in
theorem splitRecorder_run_left
    (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (cache : σ) (leftRecord rightRecord : Record)
    (hfresh : RecorderView.CacheView.cacheOf cache input = none) (hleft : leftKeep input cache) :
    ((RecorderView.recorderOf leftKeep rightKeep) (Sum.inr input)).run
        (cache, leftRecord, rightRecord) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (RecorderView.CacheView.update cache input value,
          (leftRecord ++ [(input, value)], rightRecord))) : ProbComp _) := by
  classical
  rw [RecorderView.recorderOf_run_inr_none _ _ input (cache, leftRecord, rightRecord) hfresh]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  refine congrArg (fun step => ($ᵗ HashOutput : ProbComp HashOutput) >>= step) ?_
  funext value
  rw [RecorderView.appendedOf_of_left _ _ input (cache, leftRecord, rightRecord) value
    hfresh hleft]

open scoped Classical in
theorem splitRecorder_run_right
    (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (cache : σ) (leftRecord rightRecord : Record)
    (hfresh : RecorderView.CacheView.cacheOf cache input = none)
    (hleft : ¬ leftKeep input cache) (hright : rightKeep input cache) :
    ((RecorderView.recorderOf leftKeep rightKeep) (Sum.inr input)).run
        (cache, leftRecord, rightRecord) =
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
        (pure (value, (RecorderView.CacheView.update cache input value,
          (leftRecord, rightRecord ++ [(input, value)]))) : ProbComp _) := by
  classical
  rw [RecorderView.recorderOf_run_inr_none _ _ input (cache, leftRecord, rightRecord) hfresh]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  refine congrArg (fun step => ($ᵗ HashOutput : ProbComp HashOutput) >>= step) ?_
  funext value
  rw [RecorderView.appendedOf_of_right _ _ input (cache, leftRecord, rightRecord) value
    hfresh hleft hright]

open scoped Classical in
theorem splitRecorder_run_other
    (leftKeep rightKeep : Bytes → σ → Prop) (input : Bytes)
    (cache : σ) (records : Record × Record)
    (hskip : ¬ (RecorderView.CacheView.cacheOf cache input = none ∧ leftKeep input cache))
    (hskip' : ¬ (RecorderView.CacheView.cacheOf cache input = none ∧ rightKeep input cache)) :
    ((RecorderView.recorderOf leftKeep rightKeep) (Sum.inr input)).run (cache, records) =
      plainStep input cache >>= fun step =>
        (pure (step.1, (step.2, records)) : ProbComp _) :=
  recorderOf_run_inr_plain leftKeep rightKeep input cache records hskip hskip'

/-! ### The priority the two recorders have to share

Both recorders try the **left** test first. That is a property of two separately written
if-else chains and nothing in the types enforces it, so an input that is fresh and accepted by
*both* tests is where a future edit could make them disagree — and the disagreement would not be
a failure, it would be two different recordings with the same law everywhere else.

The two lemmas below are that case, named. They are instances of the branch lemmas above with
`rightKeep` **present** rather than absent, which is the whole point: a reader can see that the
contested case was considered, and an edit that reversed either priority stops here instead of
inside the factorisation's induction. -/

/-! ### The two blocks commute past an irrelevant draw -/

/-- A draw neither block answers commutes past both of them. -/
theorem evalDist_comm_blocks {β γ : Type} (draw : ProbComp β)
    (leftLength rightLength : Nat)
    (continuation : β → List HashOutput → List HashOutput → ProbComp γ) :
    𝒟[draw >>= fun value => padding leftLength >>= fun leftTape =>
        padding rightLength >>= fun rightTape => continuation value leftTape rightTape] =
      𝒟[padding leftLength >>= fun leftTape => padding rightLength >>= fun rightTape =>
        draw >>= fun value => continuation value leftTape rightTape] := by
  rw [OracleComp.DeferredSampling.evalDist_bind_comm draw (padding leftLength)
    (fun value leftTape => padding rightLength >>= fun rightTape =>
      continuation value leftTape rightTape)]
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left (padding leftLength) _ _
    fun leftTape => ?_
  exact OracleComp.DeferredSampling.evalDist_bind_comm draw (padding rightLength)
    fun value rightTape => continuation value leftTape rightTape

/-! ## Overwriting an unread block cell

The charge resamples one cell of the target block and needs the *selection* of that cell — the
run having got as far as reading it — to hold still. It does, and for the plainest reason: the
run reads cell `index` of the target block when it makes its `index + 1`-st target query, and
whether it makes that query is settled before. So the event "the target recording grows by more
than `index`" has the same probability under any overwrite of cell `index`.

This is a statement about *conditional* probabilities, and that is what makes the whole route
affordable: the run keeps its coins and its out-of-class answers inline, and only the two class
blocks have to be front-loaded. A selection that had to be a *function* of the block would need
every draw the run makes to be presampled instead.

Past the cell the two runs do diverge — they cache different answers at the same input — so the
induction cannot be carried through it. It does not have to be: at the step that reads the cell
the event has already come true, and a recording that only grows keeps it true. -/

/-- The target recording of a state. -/
def rightOf (state : SplitTapeState σ) : Record := state.2.2.2

open scoped Classical in
/-- **One step never fails and appends at most one target entry.** Both halves of this are what
the selection argument needs, and both are read off the same case split. -/
theorem splitTapeRecorder_step (leftKeep rightKeep : Bytes → σ → Prop)
    (queried : OracleWorld.Domain) (state : SplitTapeState σ) :
    prFail (((splitTapeRecorder leftKeep rightKeep) queried).run state) = 0 ∧
      ∀ step ∈ support (((splitTapeRecorder leftKeep rightKeep) queried).run state),
        rightOf state <+: rightOf step.2 := by
  classical
  obtain ⟨cache, ⟨leftTape, rightTape⟩, ⟨leftRecord, rightRecord⟩⟩ := state
  rcases queried with coin | input
  · rw [splitTapeRecorder_run_inl]
    refine ⟨by simp, fun step hstep => ?_⟩
    rw [mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
  · by_cases hfresh : RecorderView.CacheView.cacheOf cache input = none
    · by_cases hleft : leftKeep input cache
      · cases leftTape with
        | nil =>
          rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input cache rightTape
            leftRecord rightRecord hfresh hleft]
          refine ⟨by simp, fun step hstep => ?_⟩
          rw [mem_support_bind_iff] at hstep
          obtain ⟨value, -, hpure⟩ := hstep
          rw [support_pure, Set.mem_singleton_iff] at hpure
          rw [hpure]
          exact List.prefix_rfl
        | cons head rest =>
          rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input cache head rest
            rightTape leftRecord rightRecord hfresh hleft]
          refine ⟨by simp, fun step hstep => ?_⟩
          rw [support_pure, Set.mem_singleton_iff] at hstep
          rw [hstep]
          exact List.prefix_rfl
      · by_cases hright : rightKeep input cache
        · cases rightTape with
          | nil =>
            rw [splitTapeRecorder_run_right_nil leftKeep rightKeep input cache leftTape
              leftRecord rightRecord hfresh hleft hright]
            refine ⟨by simp, fun step hstep => ?_⟩
            rw [mem_support_bind_iff] at hstep
            obtain ⟨value, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure]
            exact List.prefix_append _ _
          | cons head rest =>
            rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input cache leftTape head
              rest leftRecord rightRecord hfresh hleft hright]
            refine ⟨by simp, fun step hstep => ?_⟩
            rw [support_pure, Set.mem_singleton_iff] at hstep
            rw [hstep]
            exact List.prefix_append _ _
        · rw [splitTapeRecorder_run_other leftKeep rightKeep input cache (leftTape, rightTape)
            (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2)]
          refine ⟨by simp, fun step hstep => ?_⟩
          rw [mem_support_bind_iff] at hstep
          obtain ⟨value, -, hpure⟩ := hstep
          rw [support_pure, Set.mem_singleton_iff] at hpure
          rw [hpure]
          exact List.prefix_rfl
    · rw [splitTapeRecorder_run_other leftKeep rightKeep input cache (leftTape, rightTape)
        (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1)]
      refine ⟨by simp, fun step hstep => ?_⟩
      rw [mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact List.prefix_rfl

/-! ## Resampling one cell of the target block

The charge on one cell is the leave-one-out step, moved to the run. Three things make it go through, and each is proved above rather than assumed:
the disclosures sit on the *other* block, so overwriting a target cell cannot move them; the
cell's own value is what the coverage test reads, so overwriting it replaces that value by a
fresh one; and the selection does not see the cell.

What comes out is the per-cell factor the expectation form needs: the charge on cell `index` is
the probability that the run *got that far*, times the rate — and summing those probabilities
over the cells is an expected recording length, not a block length. -/

/-- **Overwriting one cell of a block with a fresh draw is drawing the block.** -/
theorem evalDist_padding_set {γ : Type} :
    ∀ (length index : Nat), index < length →
      ∀ (continuation : List HashOutput → ProbComp γ),
        𝒟[padding length >>= continuation] =
          𝒟[padding length >>= fun tape =>
              ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
                continuation (tape.set index value)] := by
  intro length
  induction length with
  | zero => intro index hindex; exact absurd hindex (by omega)
  | succ remaining ih =>
    intro index hindex continuation
    cases index with
    | zero =>
      simp only [padding_succ_bind, List.set_cons_zero]
      refine Eq.trans (OracleComp.DeferredSampling.evalDist_bind_comm _ (padding remaining)
        fun value rest => continuation (value :: rest)) ?_
      exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        ($ᵗ HashOutput : ProbComp HashOutput) (by simp) _).symm
    | succ smaller =>
      simp only [padding_succ_bind, List.set_cons_succ]
      refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun head => ?_
      exact ih smaller (by omega) fun rest => continuation (head :: rest)

/-- A cell read back after it was overwritten is the value it was overwritten with. -/
theorem eq_of_getElem?_set (tape : List HashOutput) (index : Nat) (value other : HashOutput)
    (hread : (tape.set index value)[index]? = some other) : other = value := by
  by_cases hlt : index < tape.length
  · rw [List.getElem?_set_self (by simpa using hlt)] at hread
    exact (Option.some_inj.mp hread).symm
  · rw [List.getElem?_eq_none (by simpa using Nat.not_lt.mp hlt)] at hread
    exact absurd hread (by simp)

open scoped Classical in
/-- A constant conjunct factors out of an event. -/
theorem probEvent_const_and {γ : Type} (run : ProbComp γ) (constant : Prop)
    (event : γ → Prop) :
    Pr{let value ← run}[constant ∧ event value] =
      if constant then Pr{let x ← run}[event x] else 0 := by
  classical
  by_cases hconstant : constant
  · rw [if_pos hconstant]
    exact probEvent_congr' (fun _ _ => ⟨fun h => h.2, fun h => ⟨hconstant, h⟩⟩) rfl
  · rw [if_neg hconstant]
    exact probEvent_eq_zero fun _ _ h => hconstant h.1

/-! ## The charge over all the cells

Summing the per-cell charge is where the expectation appears. Each cell contributes the
probability that the run reached it, and `∑ index, Pr[reached index]` is the expected number of
cells reached — the expected length of the target recording, which is the observable the budget
speaks about. Nothing here needs the recording to be short; the block length bounds the sum only
in the sense that a run cannot reach past the block, and that is a cap on the *count*, not on
the charge. -/

/-- A finite sum and a `tsum` over `ℝ≥0∞` may be exchanged. -/
theorem sum_tsum_comm {Index Result : Type} [DecidableEq Index] (indices : Finset Index)
    (summand : Index → Result → ℝ≥0∞) :
    ∑ index ∈ indices, ∑' result : Result, summand index result =
      ∑' result : Result, ∑ index ∈ indices, summand index result := by
  refine Finset.induction_on indices ?_ ?_
  · simp
  · intro head rest hhead ih
    rw [Finset.sum_insert hhead, ih, ← ENNReal.tsum_add]
    refine tsum_congr fun result => ?_
    rw [Finset.sum_insert hhead]

/-! ## The recording is the block, cell for cell

The charge is stated at cell `index` of the target *block*, and the game's event is about the
`index`-th entry of the target *recording*. They are the same answer: the recorder takes each
fresh target answer off the head of the block, in order, so the recording's answers are the
block's cells until the block runs out. Past that the recorder draws for itself and the two
part company, which is why the agreement is claimed only where the block still has a cell. -/

/-- A prefix decides the cells it covers. -/
theorem getElem?_of_prefix {β : Type} {short long : List β} (hprefix : short <+: long)
    (index : Nat) (hindex : index < short.length) : long[index]? = short[index]? := by
  obtain ⟨extra, hextra⟩ := hprefix
  rw [← hextra, List.getElem?_append_left hindex]

/-! ## The disclosing recording is its own block, cell for cell

The mirror of the target recording's correspondence, for the other head. The charge reads the disclosures off the
whole left *block*, including the part no query reached; the game's event is witnessed by the
left *recording*. They agree where the block still has a cell, which — the block being drawn as
long as the signing limit allows — is everywhere the recording reaches. -/

/-- The disclosing recording of a state. -/
def leftOf (state : SplitTapeState σ) : Record := state.2.2.1

open scoped Classical in
/-- **One step appends at most one disclosing entry.** The `leftOf` half of
`splitTapeRecorder_step`, named separately because the repaired recorder reuses it at the
noticed carrier. -/
theorem leftOf_step (leftKeep rightKeep : Bytes → σ → Prop)
    (queried : OracleWorld.Domain) (state : SplitTapeState σ)
    (step : OracleWorld.Range queried × SplitTapeState σ)
    (hstep : step ∈ support (((splitTapeRecorder leftKeep rightKeep) queried).run state)) :
    leftOf state <+: leftOf step.2 := by
  classical
  revert hstep
  obtain ⟨cache, ⟨leftTape, rightTape⟩, ⟨leftRecord, rightRecord⟩⟩ := state
  intro hstep
  rcases queried with coin | input
  · rw [splitTapeRecorder_run_inl, mem_support_bind_iff] at hstep
    obtain ⟨value, -, hpure⟩ := hstep
    rw [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
  · by_cases hfresh : RecorderView.CacheView.cacheOf cache input = none
    · by_cases hleft : leftKeep input cache
      · cases leftTape with
        | nil =>
          rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input cache rightTape
            leftRecord rightRecord hfresh hleft, mem_support_bind_iff] at hstep
          obtain ⟨value, -, hpure⟩ := hstep
          rw [support_pure, Set.mem_singleton_iff] at hpure
          rw [hpure]
          exact List.prefix_append _ _
        | cons head rest =>
          rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input cache head rest
            rightTape leftRecord rightRecord hfresh hleft, support_pure,
            Set.mem_singleton_iff] at hstep
          rw [hstep]
          exact List.prefix_append _ _
      · by_cases hright : rightKeep input cache
        · cases rightTape with
          | nil =>
            rw [splitTapeRecorder_run_right_nil leftKeep rightKeep input cache leftTape
              leftRecord rightRecord hfresh hleft hright, mem_support_bind_iff] at hstep
            obtain ⟨value, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure]
            exact List.prefix_rfl
          | cons head rest =>
            rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input cache leftTape head
              rest leftRecord rightRecord hfresh hleft hright, support_pure,
              Set.mem_singleton_iff] at hstep
            rw [hstep]
            exact List.prefix_rfl
        · rw [splitTapeRecorder_run_other leftKeep rightKeep input cache
            (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hleft h.2)
            (fun h => hright h.2), mem_support_bind_iff] at hstep
          obtain ⟨value, -, hpure⟩ := hstep
          rw [support_pure, Set.mem_singleton_iff] at hpure
          rw [hpure]
          exact List.prefix_rfl
    · rw [splitTapeRecorder_run_other leftKeep rightKeep input cache
        (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hfresh h.1)
        (fun h => hfresh h.1), mem_support_bind_iff] at hstep
      obtain ⟨value, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure]
      exact List.prefix_rfl

end SlhDsaSecurity.TapeFactor
