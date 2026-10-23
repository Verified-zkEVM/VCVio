/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheReplay
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedSplit
public import HashSig.SLHDSA.SHAKE128s.Proof.StrippedGame

/-!
# Where a cache entry came from

`CacheReplay.cached_of_queriesUnder` goes one way: an input a run consults is in the cache it
leaves. Provenance needs the other way, and it is the step only the game's structure gives —
**an entry that was not there before was made by a query**. A cache in this model is written
only by the oracle, so an entry the run ends with and did not start with is one its own handler
installed, and the input it installed it at is one the run consulted.

The two directions are not the same statement and neither implies the other. `replay` answers
`default` at an absent input, so a run can consult an input without the *replayed* evaluation
noticing, which is why the forward direction needs its own proof; and a cache can hold an entry
the run never asked at, if it was already there, which is why this direction needs the entry to
be fresh.

The proof is the same induction as `cache_value_persists`, read for its contrapositive at each
step: a query either is the probe — and then the head of the bind consults it — or is not, and
then the step leaves the probe absent, so the continuation must be the one that installed it.

The restriction to `OracleComp HashSpec` is the same one `CacheReplay` carries and for the same
reason, and it costs nothing here: every phase of the game that touches the cache other than
the adversary's own handler is a hash-only computation lifted into the game's world, and
`WarmedSplit.run_rom_liftM` routes its run back to `randomOracle` alone.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.CacheProvenance

open Security CacheReplay

/-- **A hash-only run that ends holding an entry it did not start with consulted that input**,
and the consultation may be read at any cache extending the one the run left.

The later cache is quantified in the statement rather than fixed at the run's own, for the same
reason `WarmedSplit.run_eq_replay_of_subset` does it: `QueriesUnder` is a statement *about* a
cache — it picks each continuation by `replay`ing the head — so a witness at a sub-run's own
final cache says nothing at the whole run's, and the sub-run's path is only pinned down once.
Every input along that path is in the sub-run's final cache, so a cache extending it replays
the path identically. -/
theorem queriesUnder_of_fresh_subset {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache laterCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output)
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder laterCache computation probe := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    simp only [Prod.mk.injEq] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact absurd hfresh hpresent
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases eq_or_ne probe input with rfl | hne
    · exact QueriesUnder.head probe next
    · have hstepfresh : step.2 probe = none := by
        rcases step_shape input initialCache step hstep with hshape | hshape
        · rw [hshape, QueryCache.cacheQuery_of_ne initialCache step.1 hne]
          exact hfresh
        · rw [hshape]
          exact hfresh
      have hfinal : finalCache input = some step.1 :=
        cache_value_persists (next step.1) step.2 finalCache result hrest input step.1
          (step_cached input initialCache step hstep)
      refine QueriesUnder.tail input probe next ?_
      rw [show replay laterCache input = step.1 from by
        simp [replay, hlater input step.1 hfinal]]
      exact ih step.1 step.2 result hrest hstepfresh

/-- **The same, for a hash-only computation lifted into the game's world.** Key generation, the
signer and the verifier are all of this shape, so this is the form provenance uses on them. -/
theorem queriesUnder_of_fresh_liftM {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache laterCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (liftM computation : OracleComp OracleWorld α)).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output)
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder laterCache computation probe := by
  rw [WarmedSplit.run_rom_liftM] at hmem
  exact queriesUnder_of_fresh_subset computation initialCache finalCache laterCache result hmem
    hlater probe hfresh hpresent

/-- The same again, for `OracleComp.liftComp`, which is the spelling `StrippedGame.sign_lift`
leaves the signer in. -/
theorem queriesUnder_of_fresh_liftComp {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache laterCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (OracleComp.liftComp computation OracleWorld)).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output)
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder laterCache computation probe := by
  rw [StrippedGame.run_liftComp] at hmem
  exact queriesUnder_of_fresh_subset computation initialCache finalCache laterCache result hmem
    hlater probe hfresh hpresent

/-! ## The three honest phases, as the game spells them

Each is stated with the later cache free, because each sits inside the run and the provenance
that consumes it is about the run's *final* cache. -/

/-- **A `PRF_msg` entry key generation installed is one key generation consulted.** -/
theorem queriesUnder_keygenInternal_of_fresh (secretSeed prfSeed publicSeed : Digest)
    (initialCache finalCache laterCache : QueryCache HashSpec) (keys : SecretKey × PublicKey)
    (hmem : (keys, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.keygenInternal secretSeed prfSeed publicSeed :
        OracleComp OracleWorld (SecretKey × PublicKey))).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output)
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder laterCache
      (Scheme.keygenInternal (m := OracleComp HashSpec) secretSeed prfSeed publicSeed) probe := by
  rw [WarmedSplit.keygenInternal_liftM] at hmem
  exact queriesUnder_of_fresh_liftM _ initialCache finalCache laterCache keys hmem hlater probe
    hfresh hpresent

/-- **An entry a signing request installed is one the signer consulted.** -/
theorem queriesUnder_sign_of_fresh (sk : SecretKey) (request : Message)
    (initialCache finalCache laterCache : QueryCache HashSpec) (answer : Option Bytes)
    (hmem : (answer, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output)
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder laterCache (Scheme.sign (m := OracleComp HashSpec) sk request) probe := by
  rw [StrippedGame.sign_lift] at hmem
  exact queriesUnder_of_fresh_liftComp _ initialCache finalCache laterCache answer hmem hlater
    probe hfresh hpresent

/-- **An entry verification installed is one the verifier consulted.** -/
theorem queriesUnder_verify_of_fresh (pk : PublicKey) (request : Message) (signature : Bytes)
    (initialCache finalCache laterCache : QueryCache HashSpec) (verified : Bool)
    (hmem : (verified, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.verify pk request signature : OracleComp OracleWorld Bool)).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output)
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : finalCache probe ≠ none) :
    QueriesUnder laterCache (Scheme.verify (m := OracleComp HashSpec) pk request signature)
      probe := by
  rw [WarmedSplit.verify_liftM] at hmem
  exact queriesUnder_of_fresh_liftM _ initialCache finalCache laterCache verified hmem hlater
    probe hfresh hpresent

/-! ## The signer's own randomiser query

The signer's first call, on a request it serves, is the `PRF_msg` query for that request's
framing. The randomiser defect's charge is about the *answer* to that query, so what provenance
has to hand on is not only that the signer consulted the input but that the entry is **there**
— an absent entry would make `replay` answer `default` and turn the coincidence into a
statement about a fixed constant, which no per-run charge can pay for. -/

/-- **A served request consults its own `PRF_msg` input.** -/
theorem queriesUnder_sign_randomizer (cache : QueryCache HashSpec) (sk : SecretKey)
    (request : Message) (framed : Bytes) (hframe : request.frame = some framed) :
    QueriesUnder cache (Scheme.sign (m := OracleComp HashSpec) sk request)
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) := by
  rw [Scheme.sign, hframe]
  refine queriesUnder_bind cache _ _ _ ?_
  rw [Scheme.signInternal]
  exact queriesUnder_shortHash cache _ _

/-- **And leaves its answer in the cache, with the answer named.**

**The name is the point.** A conclusion that the entry is merely present leaves the consumer to
recover the value through `CacheReplay.replay`, which answers a miss with `default` — so a
statement built on presence alone cannot distinguish the signer's own randomiser from
`Hashing.truncate default`, and an adversary that queries at that byte string refutes it. The
third component says what `replay` returns here, which is what makes the distinction expressible
at all; a consumer that only wants presence has `sign_randomizer_cached` below.

Read at any cache extending the one the sub-run left: the value is the same at both, which is
the containment the consumers need beside the answer. -/
theorem sign_randomizer_answer (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed)
    (initialCache finalCache laterCache : QueryCache HashSpec) (answer : Option Bytes)
    (hmem : (answer, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output) :
    ∃ value : HashOutput,
      finalCache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some value ∧
        laterCache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = some value ∧
          HonestProbes.replayRandomizer laterCache sk framed = Hashing.truncate value := by
  rw [StrippedGame.sign_lift, StrippedGame.run_liftComp] at hmem
  have hcached := cached_of_queriesUnder (Scheme.sign (m := OracleComp HashSpec) sk request)
    initialCache finalCache answer _
    (queriesUnder_sign_randomizer finalCache sk request framed hframe) hmem
  cases hentry : finalCache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) with
  | none => exact absurd hentry hcached
  | some value =>
    refine ⟨value, rfl, hlater _ value hentry, ?_⟩
    rw [HonestProbes.replayRandomizer]
    simp [replay, hlater _ value hentry]

/-- **And leaves its answer in the cache**, read at any cache extending the one it left. The
presence-only reading of `sign_randomizer_answer`.

**Which consumers need which**, so that this entry is annotated rather than re-reported:

* `ServedRandomised.signerRandomised_of_served` needs **presence only**. It wants "cached with
  some value" and recovers the value itself by `Option.ne_none_iff_exists'`, so the drop costs
  it nothing.
* `PhaseProvenance.SignerMade`'s second conjunct, and through it the provenance hypothesis,
  needed the **value**. It compares the signer's *published* randomiser against what
  `CacheReplay.replay` returns, and `replay` answers a miss with `default` — so a statement
  carried on presence alone said something about `Hashing.truncate default` for messages never
  signed, and a one-query adversary refuted it. That is what `sign_randomizer_answer` fixes.

So a presence-only conclusion is a defect **when a consumer must relate the value to something
else**, and merely conservative when the consumer can recover it. The `≠ none` grep finds the
candidates; only a consumer says which are live. -/
theorem sign_randomizer_cached (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed)
    (initialCache finalCache laterCache : QueryCache HashSpec) (answer : Option Bytes)
    (hmem : (answer, finalCache) ∈ support ((simulateQ KeygenUniform.rom
      (Scheme.sign sk request : OracleComp OracleWorld (Option Bytes))).run initialCache))
    (hlater : ∀ (input : Bytes) (output : HashOutput),
      finalCache input = some output → laterCache input = some output) :
    laterCache (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) ≠ none := by
  obtain ⟨value, -, hvalue, -⟩ :=
    sign_randomizer_answer sk request framed hframe initialCache finalCache laterCache answer
      hmem hlater
  rw [hvalue]
  exact Option.some_ne_none value

/-! ## The signer's own digest query

The randomiser's query is the signer's first; the digest's is its second, and it is the one that
decides **which FORS positions the signature opens**. A disclosure claim read off the signing log
needs both entries present, not merely the returned bytes: `CacheReplay.replay` answers `default`
at an absent input, so an equation between replayed signatures says nothing about what the cache
holds, and `CacheAvailability.signedAt` is a statement about what the cache holds. -/

/-! ## One query of the game's own world

The adversary's handler forwards a world query and the cache is written by that query alone, so
an entry that appears across one step appears at the input the step asked at — and a coin asks
at nothing. This is the one place provenance cannot go through `CacheReplay`, since a coin is
not a hash call. -/

/-- **A single world query installs an entry only at its own hash input.** -/
theorem queried_of_fresh_step (queried : OracleWorld.Domain)
    (initialCache : QueryCache HashSpec)
    (step : OracleWorld.Range queried × QueryCache HashSpec)
    (hstep : step ∈ support ((simulateQ KeygenUniform.rom
      (liftM (OracleWorld.query queried) :
        OracleComp OracleWorld (OracleWorld.Range queried))).run initialCache))
    (probe : Bytes) (hfresh : initialCache probe = none) (hpresent : step.2 probe ≠ none) :
    queried = Sum.inr probe := by
  rw [show (simulateQ KeygenUniform.rom
      (liftM (OracleWorld.query queried) :
        OracleComp OracleWorld (OracleWorld.Range queried))) = KeygenUniform.rom queried from by
    simp] at hstep
  rcases queried with coin | input
  · obtain ⟨value, hvalue⟩ : step ∈ Set.range fun answer => (answer, initialCache) := by
      simpa [KeygenUniform.rom, Xmss.RandomOracleModel.impl, unifFwdImpl] using hstep
    exact absurd (show step.2 probe = none from by rw [← hvalue]; exact hfresh) hpresent
  · have hrom : step ∈ support ((randomOracle input).run initialCache) := hstep
    rcases step_shape input initialCache step hrom with hshape | hshape
    · rcases eq_or_ne probe input with rfl | hne
      · rfl
      · exact absurd (show step.2 probe = none from by
          rw [hshape, QueryCache.cacheQuery_of_ne initialCache step.1 hne]
          exact hfresh) hpresent
    · exact absurd (show step.2 probe = none from by rw [hshape]; exact hfresh) hpresent

end SlhDsaSecurity.CacheProvenance
