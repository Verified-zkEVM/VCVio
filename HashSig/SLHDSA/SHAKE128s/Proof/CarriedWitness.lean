/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RecorderView

/-!
# The recorder at the carrier, with the flag deciding and the served set remembering

The disclosing test is `HandlerCarrier.FilesLeft` — a query made while the signing oracle holds
its framing up, at an input of that request's own digest shape — and the predicate the
recording's entries satisfy at the end is `HandlerCarrier.Served`, membership of the carrier's
served multiset.

**The two are different predicates, and the reason is one sentence: a cache-readable test is
monotone because it is forgeable.** An adversary holding `SK.prf` can put the `PRF_msg` entry a
cache test looks for into the cache with no request behind it. A flag cannot be forged, because
only the signing oracle sets it, but a flag is down again by the end of the run, so it cannot
also be the thing an entry satisfies at the end. Splitting the roles lets the test be
unforgeable and the record readable at once; `RecorderView.noticing_left_recordOf_endKeep_final`
is where the split is paid for: filing puts the input into the served set, and no later step
takes it out. The remaining link to the signing log is `ServingCarrier.AgreesWithLog`, a fact
about the signing oracle rather than an assumption about the adversary.

**The notice files and the install caches.** `servingView` is a legal `CacheView` because the
law constrains only the cache, and filing does not touch it.

**A test that reads a flag can only be instantiated at a presentation that sets the flag**:
`FilesLeft` is *empty* wherever nothing frames, so the left test and the tail have to move
together.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CarriedWitness

open RecorderView HandlerCarrier

variable (pk : PublicKey)

/-! ## The view

**Filing is not installing.** The notice runs at every hash query, hit or miss; the install runs
on a miss. A served request whose digest input was already cached is therefore still filed: an
input is installed once and is never fresh again, so it could not be filed later.

Filing and caching still happen in the same step, which is what disclosure beginning exactly
where the answer does means. -/

open scoped Classical in
/-- Notice a query: file the input when the flag says the signer is serving it. -/
noncomputable def servingNotice (state : State) (input : Bytes) : State :=
  if FilesLeft pk state input then file state input else state

open scoped Classical in
/-- **Filing does not touch the cache**, which is the law the view owes. -/
theorem cacheOf_servingNotice (state : State) (input : Bytes) :
    cacheOf (servingNotice pk state input) = cacheOf state := by
  classical
  rw [servingNotice]
  split <;> rfl

open scoped Classical in
/-- **Nor the framing**, so the test reads the same before and after the notice. -/
theorem framing_servingNotice (state : State) (input : Bytes) :
    (servingNotice pk state input).framing = state.framing := by
  classical
  rw [servingNotice]
  split <;> rfl

open scoped Classical in
/-- **So the test is blind to the notice.** -/
theorem filesLeft_servingNotice (state : State) (input probe : Bytes) :
    FilesLeft pk (servingNotice pk state probe) input ↔ FilesLeft pk state input := by
  classical
  constructor
  · rintro ⟨framed, hframing, randomizer, hinput⟩
    exact ⟨framed, by rw [← framing_servingNotice pk state probe]; exact hframing,
      randomizer, hinput⟩
  · rintro ⟨framed, hframing, randomizer, hinput⟩
    exact ⟨framed, by rw [framing_servingNotice pk state probe]; exact hframing,
      randomizer, hinput⟩

open scoped Classical in
/-- The carrier as a recorder state, with the signing oracle's own notice. -/
@[reducible] noncomputable def servingView : CacheView State where
  cacheOf := cacheOf
  update := cacheAnswer
  onQuery := servingNotice pk
  cache_update := fun _ _ _ => rfl
  cache_onQuery := cacheOf_servingNotice pk

open scoped Classical in
/-- **A filed input is served from that step on** — whether or not the step drew anything. -/
theorem served_servingNotice_self (state : State) (input : Bytes)
    (hfiles : FilesLeft pk state input) : Served (servingNotice pk state input) input := by
  classical
  rw [servingNotice, if_pos hfiles]
  exact Multiset.mem_cons_self _ _

open scoped Classical in
/-- **No notice unserves anything.** -/
theorem served_servingNotice (state : State) (input probe : Bytes)
    (hserved : Served state input) : Served (servingNotice pk state probe) input := by
  classical
  rw [servingNotice]
  split
  · exact Multiset.mem_cons_of_mem hserved
  · exact hserved

/-- **And installing an answer does not touch the served set.** -/
theorem served_cacheAnswer_iff (state : State) (input probe : Bytes) (answer : HashOutput)
    (hserved : Served state input) : Served (cacheAnswer state probe answer) input := hserved

/-! ## The two tests at the carrier -/

/-- The left test: the flag is up for a request, and the input is that request's own digest
shape. Only the signing oracle sets the flag, so there is no clause an adversary can satisfy. -/
def disclosingKeep : Bytes → State → Prop := fun input state => FilesLeft pk state input

/-- What an entry of the disclosing recording satisfies at the end: the carrier served it. -/
def disclosedAtEnd : Bytes → State → Prop := fun input state => Served state input

open scoped Classical in
/-- **Every entry of the disclosing recording was served**, read at the end of the run. The flag
decided each entry when it was noticed; the served set is what remembers. -/
theorem mem_served_of_mem_leftRecord {α : Type} (rightKeep : Bytes → State → Prop)
    (computation : OracleComp OracleWorld α) (state : StateOf State)
    (result : α × StateOf State)
    (hmem : result ∈ support ((simulateQ (@noticingRecorderOf State (servingView pk)
      (disclosingKeep pk) rightKeep) computation).run state))
    (hstart : ∀ entry ∈ state.2.1, Served state.1 entry.1) :
    ∀ entry ∈ result.2.2.1, Served result.2.1 entry.1 :=
  @noticing_left_recordOf_endKeep_final State (servingView pk) α (disclosingKeep pk) rightKeep
    disclosedAtEnd
    (fun input view hkeep =>
      served_servingNotice_self pk view input
        ((filesLeft_servingNotice pk view input input).mp hkeep))
    (fun input probe view hkeep => served_servingNotice pk view input probe hkeep)
    (fun input probe view answer _ hkeep =>
      served_cacheAnswer_iff view input probe answer hkeep)
    computation state result hmem hstart

end SlhDsaSecurity.CarriedWitness
