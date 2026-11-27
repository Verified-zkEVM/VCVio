/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.SyncSignatureAlg.Unforgeability
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling

/-!
# Answering signing queries with a signer that queries an ideal PRF

Some synchronized signature schemes derive their signing randomness from a PRF. This file models
such a signer as a `SyncSignatureAlg` over `OracleComp (PRFScheme.PRFOracleSpec D Response)`: it
may sample uniformly and query a function `D → Response`. When that function is a random function,
the signer should behave like a direct signer that samples its randomness itself. This file states
and proves that comparison for a whole unforgeability adversary, including repeated epochs and
failed signatures.

`signingHandler` answers the adversary's queries: it passes uniform sampling through and answers
signing queries with the scheme's signing oracle `SyncSignatureAlg.signingOracle`, which records
each epoch's first request in a `SyncSignatureAlg.History`. The signer's function queries are left
open. `idealHandler` answers those function queries with the ideal PRF handler
`PRFScheme.prfIdealQueryImpl` and keeps the signing history and the PRF cache as one state.
`simulateQ_prfIdeal_signingHandler_run` relates it to running the two handlers one after the
other.

The ideal handler caches whole PRF responses, so a later function query at a cached input returns
the same response. `idealHandler_run_evalDistEq` is the main result. It assumes that, while a
freshness invariant on the history and cache holds, one signing call at an unused epoch has the
distribution of the direct signer and keeps the invariant. It concludes that running any program
with `idealHandler` and then dropping the cache has the distribution of
`SyncSignatureAlg.runWithSigningOracle` with the direct signer.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Definition 8 (SY-UF-CMA).
-/

public section
namespace SyncSignatureAlg.PRFSimulation
open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

variable {D Response M PK SK Sig E : Type} [DecidableEq E]

/-- Answer the adversary's queries with a signer that queries a PRF. Uniform sampling passes
through, and signing queries go to `alg.signingOracle sk`. The result still makes the signer's
function queries. -/
@[expose] def signingHandler
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) : QueryImpl (unifSpec + signingSpec E M Sig)
      (StateT (History E M Sig) (OracleComp (PRFScheme.PRFOracleSpec D Response))) :=
  let forward : QueryImpl unifSpec (OracleComp (PRFScheme.PRFOracleSpec D Response)) :=
    fun q => liftM (OracleSpec.query (Sum.inl q) :
      OracleQuery (PRFScheme.PRFOracleSpec D Response) _)
  forward.liftTarget (StateT (History E M Sig)
    (OracleComp (PRFScheme.PRFOracleSpec D Response))) + alg.signingOracle sk

/-- Only a signing query at an unused epoch runs the signer. So if each signer call makes at most
`budget` function queries, one adversary query makes at most `budget` function queries when it is
a signing query and none when it is a uniform-sampling query. -/
theorem signingHandler_query_bound
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) (budget : ℕ)
    (hsign : ∀ ep msg, IsQueryBoundP (alg.sign sk ep msg) (fun q => q.isRight = true) budget)
    (query : (unifSpec + signingSpec E M Sig).Domain) (history : History E M Sig) :
    IsQueryBoundP ((signingHandler alg sk query).run history)
      (fun q => q.isRight = true) (if query.isRight then budget else 0) := by
  cases query with
  | inl q =>
      simp only [signingHandler, QueryImpl.add_apply_inl]
      unfold QueryImpl.liftTarget
      simp
  | inr request =>
      rcases request with ⟨ep, msg⟩
      change IsQueryBoundP (alg.signingOracle sk (ep, msg) history)
        (fun q => q.isRight = true) budget
      cases hused : history ep with
      | some previous =>
          rcases previous with ⟨first, answer⟩
          rw [signingOracle_used (h := hused)]
          trivial
      | none =>
          rw [signingOracle_unused (h := hused)]
          change IsQueryBoundP (alg.sign sk ep msg >>= fun answer =>
            pure (answer, Function.update history ep (some (msg, answer))))
            (fun q => q.isRight = true) budget
          simpa only [Nat.add_zero] using isQueryBoundP_bind (hsign ep msg) (fun answer _ =>
            (show IsQueryBoundP (pure
              (answer, Function.update history ep (some (msg, answer))) :
                OracleComp (PRFScheme.PRFOracleSpec D Response) _)
              (fun q => q.isRight = true) 0 from trivial))

/-- Answer the adversary's queries with `signingHandler`, and the signer's function queries with
the ideal PRF handler. The state is the signing history together with the PRF cache. -/
@[expose] def idealHandler [DecidableEq D] [SampleableType Response]
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) : QueryImpl (unifSpec + signingSpec E M Sig)
      (StateT (History E M Sig × (D →ₒ Response).QueryCache) ProbComp) :=
  (PRFScheme.prfIdealQueryImpl.mapStateTBase (signingHandler alg sk)).flattenStateT

section idealHandler

variable [DecidableEq D] [SampleableType Response]

/-- Running a program with `signingHandler` and then answering the remaining function queries
with the ideal PRF handler gives the run with `idealHandler`, up to reassociating the state. -/
theorem simulateQ_prfIdeal_signingHandler_run
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) {A : Type} (program : OracleComp (unifSpec + signingSpec E M Sig) A)
    (history : History E M Sig) (cache : (D →ₒ Response).QueryCache) :
    (simulateQ PRFScheme.prfIdealQueryImpl
      ((simulateQ (signingHandler alg sk) program).run history)).run cache =
      (fun z : A × (History E M Sig × (D →ₒ Response).QueryCache) =>
        ((z.1, z.2.1), z.2.2)) <$>
        (simulateQ (idealHandler alg sk) program).run (history, cache) :=
  simulateQ_mapStateTBase_run_eq_map_flattenStateT _ _ program history cache

/-- `simulateQ_prfIdeal_signingHandler_run` with the final cache dropped. -/
theorem simulateQ_prfIdeal_signingHandler_run'
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) {A : Type} (program : OracleComp (unifSpec + signingSpec E M Sig) A)
    (history : History E M Sig) (cache : (D →ₒ Response).QueryCache) :
    (simulateQ PRFScheme.prfIdealQueryImpl
      ((simulateQ (signingHandler alg sk) program).run history)).run' cache =
      Prod.map id Prod.fst <$> (simulateQ (idealHandler alg sk) program).run (history, cache) := by
  rw [StateT.run'_eq, simulateQ_prfIdeal_signingHandler_run, Functor.map_map]
  rfl

/-- A uniform-sampling query passes through `idealHandler` and changes neither state. -/
theorem idealHandler_inl
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) (q : ℕ) (history : History E M Sig) (cache : (D →ₒ Response).QueryCache) :
    (idealHandler alg sk (Sum.inl q)).run (history, cache) =
      (fun response => (response, (history, cache))) <$>
        (liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) := by
  simp [idealHandler, signingHandler, PRFScheme.prfIdealQueryImpl,
    QueryImpl.add_apply_inl, QueryImpl.liftTarget, unifFwdImpl]

/-- A signing query at a used epoch returns `none`, makes no PRF query and changes neither the
history nor the cache. -/
theorem idealHandler_used
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) (epoch : E) (message : M) (history : History E M Sig)
    (cache : (D →ₒ Response).QueryCache) (first : M) (answer : Option Sig)
    (hused : history epoch = some (first, answer)) :
    (idealHandler alg sk (Sum.inr (epoch, message))).run (history, cache) =
      pure (none, (history, cache)) := by
  rw [idealHandler, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  change _ <$> (simulateQ PRFScheme.prfIdealQueryImpl
    (alg.signingOracle sk (epoch, message) history)).run cache = _
  rw [signingOracle_used alg sk history epoch message first answer hused]
  simp

/-- A signing query at an unused epoch runs the signer once against the ideal PRF and records the
first request and its answer, even when the answer is `none`. -/
theorem idealHandler_unused
    (alg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (sk : SK) (epoch : E) (message : M) (history : History E M Sig)
    (cache : (D →ₒ Response).QueryCache) (hunused : history epoch = none) :
    (idealHandler alg sk (Sum.inr (epoch, message))).run (history, cache) =
      (fun result => ((result.1,
        (Function.update history epoch (some (message, result.1)), result.2)) :
          (unifSpec + signingSpec E M Sig).Range (Sum.inr (epoch, message)) ×
            (History E M Sig × (D →ₒ Response).QueryCache))) <$>
        (simulateQ PRFScheme.prfIdealQueryImpl (alg.sign sk epoch message)).run cache := by
  rw [idealHandler, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  change _ <$> (simulateQ PRFScheme.prfIdealQueryImpl
    (alg.signingOracle sk (epoch, message) history)).run cache = _
  rw [signingOracle_unused alg sk history epoch message hunused, simulateQ_bind,
    StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp, Functor.map_map]

end idealHandler

section direct

variable {SK' : Type}

private theorem directHandler_inl (alg : SyncSignatureAlg ProbComp M PK SK' Sig E) (sk : SK')
    (q : ℕ) (history : History E M Sig) :
    ((unifSpec.passthrough + signingKernelOracle (alg.sign sk)) (Sum.inl q)).run history =
      (fun response => (response, history)) <$>
        (liftM (unifSpec.query q) : ProbComp (unifSpec.Range q)) := by
  simp [QueryImpl.passthrough_add, QueryImpl.add_apply_inl]

private theorem directHandler_inr (alg : SyncSignatureAlg ProbComp M PK SK' Sig E) (sk : SK')
    (request : E × M) (history : History E M Sig) :
    ((unifSpec.passthrough + signingKernelOracle (alg.sign sk)) (Sum.inr request)).run history =
      alg.signingOracle sk request history := by
  simp only [QueryImpl.passthrough_add, QueryImpl.add_apply_inr]
  rfl

end direct

/-- Running a program with `idealHandler` and dropping the final PRF cache has the distribution of
running it against the direct signer's signing oracle, `directAlg.runWithSigningOracle`.

The hypotheses concern one signing call at an unused epoch, from a history and cache satisfying
the invariant `fresh`: `hsign` says the PRF-based signer under the ideal PRF has the direct
signer's distribution, and `hpreserve` says the call keeps `fresh`. Typically `fresh` says that the
cache holds no response at the PRF inputs of any unused epoch. -/
theorem idealHandler_run_evalDistEq {SK' A : Type} [DecidableEq D] [SampleableType Response]
    (oracleAlg : SyncSignatureAlg (OracleComp (PRFScheme.PRFOracleSpec D Response)) M PK SK Sig E)
    (directAlg : SyncSignatureAlg ProbComp M PK SK' Sig E) (osk : SK) (dsk : SK')
    (fresh : History E M Sig → (D →ₒ Response).QueryCache → Prop)
    (hsign : ∀ ep msg history cache, fresh history cache → history ep = none →
      (simulateQ PRFScheme.prfIdealQueryImpl (oracleAlg.sign osk ep msg)).run' cache =ᵈ
        directAlg.sign dsk ep msg)
    (hpreserve : ∀ ep msg history cache, fresh history cache → history ep = none →
      ∀ result ∈ support
        ((simulateQ PRFScheme.prfIdealQueryImpl (oracleAlg.sign osk ep msg)).run cache),
      fresh (Function.update history ep (some (msg, result.1))) result.2)
    (program : OracleComp (unifSpec + signingSpec E M Sig) A)
    (history : History E M Sig) (cache : (D →ₒ Response).QueryCache)
    (hfresh : fresh history cache) :
    Prod.map id Prod.fst <$>
      (simulateQ (idealHandler oracleAlg osk) program).run (history, cache) =ᵈ
      directAlg.runWithSigningOracle dsk program history := by
  unfold runWithSigningOracle runWithSigningKernel
  refine evalDistEq_map_run_simulateQ_of_inv (idealHandler oracleAlg osk) _ Prod.fst
    (fun state => fresh state.1 state.2) ?_ ?_ program (history, cache) hfresh
  · rintro (q | ⟨ep, msg⟩) ⟨hist, table⟩ htable
    · rw [idealHandler_inl, directHandler_inl]
      simp [Functor.map_map]
    · rw [directHandler_inr]
      cases hused : hist ep with
      | some previous =>
          rw [idealHandler_used oracleAlg osk ep msg hist table previous.1 previous.2 hused,
            signingOracle_used directAlg dsk hist ep msg previous.1 previous.2 hused]
          simp
      | none =>
          rw [idealHandler_unused oracleAlg osk ep msg hist table hused,
            signingOracle_unused directAlg dsk hist ep msg hused, Functor.map_map,
            bind_pure_comp]
          have hmap := (hsign ep msg hist table htable hused).map
            (fun answer => (answer, Function.update hist ep (some (msg, answer))))
          rw [StateT.run'_eq, Functor.map_map] at hmap
          exact hmap
  · rintro (q | ⟨ep, msg⟩) ⟨hist, table⟩ htable result hresult
    · rw [idealHandler_inl, support_map] at hresult
      obtain ⟨_, _, rfl⟩ := hresult
      exact htable
    · cases hused : hist ep with
      | some previous =>
          rw [idealHandler_used oracleAlg osk ep msg hist table previous.1 previous.2 hused,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact htable
      | none =>
          rw [idealHandler_unused oracleAlg osk ep msg hist table hused, support_map] at hresult
          obtain ⟨signed, hsigned, rfl⟩ := hresult
          exact hpreserve ep msg hist table htable hused signed hsigned

end SyncSignatureAlg.PRFSimulation
