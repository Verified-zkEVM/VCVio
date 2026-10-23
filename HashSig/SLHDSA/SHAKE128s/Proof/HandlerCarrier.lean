/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Hashing

/-!
# The state a signing handler carries

`ServingCarrier` reads a disclosed set off a handler's state, and `ServedDisclosure` states the
notion the reading obeys. That notion is stated over `CacheAvailability`, which sits above
`OpenCache`, so the files stating it sit above the handler that has to carry it. The carrier
type `State` and its operations therefore live here, below all of them, and everything that needs
the notion stays above.

**The framing carries a frame and the served set carries digest inputs**, and the two sorts are
kept apart deliberately. Indexing the served set by the message would let an adversary pick its
own randomiser for a message the signer did sign and have its own digest's positions counted as
disclosed. Indexing by the input pins the randomiser and the message together through
`Hashing.messageInput_injective`.

**Filing happens at the query, not at completion.** The digest input is not known when a request
arrives — it depends on the randomiser the oracle has yet to answer — so the handler sets the
framing while it serves and files an input when a query matches it. Filing and caching happen in
the *same step*, so disclosure begins exactly where the answer does. Filing at completion would
disclose only *after* the signer's FORS reads.

**`FilesLeft` does not ask for freshness, and must not.** A request whose digest input is
already cached when the signer asks is still served, and if it were not filed the signer's own
reads would be unavailable at the carrier: the stalled run would read a cell it must be blind to.
The freshness rule belongs to the *coverage recorder's* list, where a block of answers has to be
a block of fresh draws; it is a different object and it does not transfer here.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.HandlerCarrier

/-- What a handler carries: the cache, the digest inputs the signer has served, and the framing
of the request it is serving. -/
structure State where
  /-- The random-oracle cache. -/
  cache : QueryCache HashSpec
  /-- The digest inputs filed as served by the signer. -/
  served : Multiset Bytes
  /-- The framed message of the signing request in flight, if any. -/
  framing : Option Bytes

/-- The digest inputs a state has served. -/
def Served (state : State) (input : Bytes) : Prop := input ∈ state.served

/-- The cache a state holds. -/
def cacheOf (state : State) : QueryCache HashSpec := state.cache

/-! ## Growth

Stated at **what the state discloses** and not at its three components. The step in which a
request completes takes its framing out of flight, and a relation that fixed the framing
component would fail at exactly that step — the step the whole notion exists for. -/

/-- Growth of a carrier: entries persist and served inputs stay served. -/
def Grows (left right : State) : Prop :=
  (∀ (input : Bytes) (answer : HashOutput),
      left.cache input = some answer → right.cache input = some answer) ∧
    ∀ input : Bytes, Served left input → Served right input

/-- Every state grows into itself. -/
theorem Grows.refl (state : State) : Grows state state := ⟨fun _ _ h => h, fun _ h => h⟩

/-- Growth is transitive. -/
theorem Grows.trans {left middle right : State} (hfirst : Grows left middle)
    (hsecond : Grows middle right) : Grows left right :=
  ⟨fun input answer hentry => hsecond.1 input answer (hfirst.1 input answer hentry),
    fun input hinput => hsecond.2 input (hfirst.2 input hinput)⟩

/-! ## The operations -/

/-- Set the framing of the request being served. -/
def setFraming (state : State) (framed : Bytes) : State := { state with framing := some framed }

/-- Clear the framing when the request is done. -/
def clearFraming (state : State) : State := { state with framing := none }

/-- File a digest input the signer has served. -/
def file (state : State) (input : Bytes) : State :=
  { state with served := input ::ₘ state.served }

/-- Cache an answer. -/
def cacheAnswer (state : State) (input : Bytes) (answer : HashOutput) : State :=
  { state with cache := state.cache.cacheQuery input answer }

@[simp] theorem framing_cacheAnswer (state : State) (input : Bytes) (answer : HashOutput) :
    (cacheAnswer state input answer).framing = state.framing := rfl

@[simp] theorem framing_file (state : State) (input : Bytes) :
    (file state input).framing = state.framing := rfl

@[simp] theorem served_cacheAnswer (state : State) (input : Bytes) (answer : HashOutput) :
    (cacheAnswer state input answer).served = state.served := rfl

/-- **Any change of framing is growth.** The relation does not constrain the component, so the
completing step — which takes a request out of flight — is growth like every other. -/
theorem grows_of_framing (state : State) (framing : Option Bytes) :
    Grows state { state with framing := framing } := Grows.refl state

/-- Setting the framing is growth. -/
theorem grows_setFraming (state : State) (framed : Bytes) :
    Grows state (setFraming state framed) := grows_of_framing state (some framed)

/-- Clearing the framing is growth. -/
theorem grows_clearFraming (state : State) : Grows state (clearFraming state) :=
  grows_of_framing state none

/-- Filing a served input is growth. -/
theorem grows_file (state : State) (input : Bytes) : Grows state (file state input) :=
  ⟨fun _ _ h => h, fun _ hprobe => Multiset.mem_cons_of_mem hprobe⟩

/-- Caching an answer at a fresh input is growth. -/
theorem grows_cacheAnswer (state : State) (input : Bytes) (answer : HashOutput)
    (hfresh : state.cache input = none) : Grows state (cacheAnswer state input answer) := by
  refine ⟨fun probe value hvalue => ?_, fun _ h => h⟩
  by_cases hequal : probe = input
  · rw [hequal, hfresh] at hvalue
    exact absurd hvalue (by simp)
  · change (state.cache.cacheQuery input answer) probe = some value
    rw [QueryCache.cacheQuery_of_ne state.cache answer hequal]
    exact hvalue

/-! ## The recorder's left test

A query made while the framing names a request, at an input of that request's own digest shape.
It reads the input and the state and nothing else, and there is no clause an adversary can
satisfy, because only the signing oracle sets the framing. -/

/-- The test the carrier files its served set by. **No freshness clause**: a served request
whose digest input was already cached is served all the same, and leaving it unfiled would make
the signer's own reads unavailable.

**The match is against the framing in flight, and must stay that way.** The natural
simplification — asking only whether *some* request is in flight, since the blindness argument
needs no more than that — is false and unrecoverable. By the FIPS 205 format identity a message
input at `m` is a `PRF_msg` input at `PK.root ‖ m`, so the signer's own randomiser query on a
request framed `f` is a message input at a message one block *shorter* than `f`; comparing
against `f` itself rejects it, and comparing against nothing
accepts it. Accepting it would put two entries per request in the disclosing recording, which
is past the Poisson coupling's **mean** and not merely past its proved tail, so the rare event
becomes the typical one and no sharpening reaches it. It would also stop the served set being
the image of the signing log.

The mean load potential at the coupling's own rate is `2 ^ 63 · T₁₄(3)`, about `2 ^ 101.75`
(`ForsConcentration.centeredLoadSum_eq` uses `T₁₄(3) = 461101962108` as its centering).
Doubling the recording doubles the per-bin rate, so the mean crosses `2 ^ 103` already at rate
about `3.34`. -/
def FilesLeft (pk : PublicKey) (state : State) (input : Bytes) : Prop :=
  ∃ framed : Bytes, state.framing = some framed ∧
    ∃ randomizer : Digest, input = Hashing.messageInput randomizer pk framed

/-- **Nothing is filed when nothing is being served.** The adversary's own queries run with the
framing clear, so the test is false at every one of them whatever they ask. -/
theorem not_filesLeft_of_clear (pk : PublicKey) (state : State) (hclear : state.framing = none)
    (input : Bytes) : ¬ FilesLeft pk state input := by
  rintro ⟨framed, hframing, -⟩
  rw [hclear] at hframing
  simp at hframing

/-- **A filed input is the in-flight request's own digest input.** -/
theorem framed_of_filesLeft (pk : PublicKey) (state : State) (input : Bytes)
    (hfiles : FilesLeft pk state input) :
    ∃ (framed : Bytes) (randomizer : Digest), state.framing = some framed ∧
      input = Hashing.messageInput randomizer pk framed := by
  obtain ⟨framed, hframing, randomizer, hinput⟩ := hfiles
  exact ⟨framed, randomizer, hframing, hinput⟩

end SlhDsaSecurity.HandlerCarrier
