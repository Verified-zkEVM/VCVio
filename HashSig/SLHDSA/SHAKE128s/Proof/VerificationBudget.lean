/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import HashSig.SLHDSA.SHAKE128s.Proof.VerificationQueries
public import HashSig.SLHDSA.SHAKE128s.Proof.VerifierNaturality

/-!
# The verification budget

The concrete experiment charges every hash query of the final verification to the `verification`
coordinate of its cost vector. This file relates that coordinate to the verifier's own query
count: the verifier only queries the hash oracle (`verify_lift`), so counting its queries in the
experiment's oracle world agrees with counting them in the hash-only world
(`verificationCount_lift`). The verifier's per-run query bounds then become bounds on the
verification coordinate (`verification_count_bounds`, `verification_accepted_count_bounds`), and
an accepted forgery costs the experiment at least `569` charged hashes
(`accepted_outcome_work`).
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.VerificationBudget

variable {α β : Type}

open Security VerificationQueries

/-- The cost vector of a query made during the final verification: its hash cost, charged to
the `verification` coordinate. -/
@[expose] def verificationCost (input : OracleWorld.Domain) : Counts :=
  Counts.single .verification (Security.hashCost input)

/-- The verifier in the experiment's oracle world is the hash-only verifier, lifted. -/
theorem verify_lift (pk : PublicKey) (request : Message) (signature : Bytes) :
    (Scheme.verify pk request signature : OracleComp OracleWorld Bool) =
      OracleComp.liftComp (Scheme.verify pk request signature : OracleComp HashSpec Bool)
        OracleWorld := by
  exact (VerifierNaturality.verify_simulate
    (fun input => query (spec := HashSpec) input : QueryImpl HashSpec (OracleComp OracleWorld))
    (fun _ => rfl) pk request signature).symm

/-- Counting the queries of a pure computation records no cost. -/
theorem countQueries_pure (cost : OracleWorld.Domain → Counts) (value : α) :
    countQueries cost (pure value) = pure (value, 0) := rfl

/-- Query counting is additive over sequencing. -/
theorem countQueries_bind (cost : OracleWorld.Domain → Counts)
    (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    countQueries cost (first >>= next) = (do
      let left ← countQueries cost first
      let right ← countQueries cost (next left.1)
      return (right.1, left.2 + right.2)) := by
  simp [countQueries, simulateQ_bind, WriterT.run_bind, bind_assoc,
    map_eq_bind_pure_comp]

/-- A single query is charged its cost. -/
theorem countQueries_query (cost : OracleWorld.Domain → Counts) (input : OracleWorld.Domain) :
    countQueries cost (liftM (OracleWorld.query input)) = (do
      let output ← liftM (OracleWorld.query input)
      return (output, cost input)) := by
  simp [countQueries, addCostOracle, QueryImpl.withAddCost, QueryImpl.withCost,
    map_eq_bind_pure_comp]

/-- The unit-cost count of a pure computation is zero. -/
theorem counted_pure (value : α) :
    counted (pure value) = pure (value, Multiplicative.ofAdd 0) := rfl

/-- The unit-cost count of a query followed by a continuation is one more than the
continuation's count. -/
theorem counted_query_bind (input : HashSpec.Domain)
    (next : HashSpec.Range input → OracleComp HashSpec α) :
    counted (liftM (HashSpec.query input) >>= next) = (do
      let output ← liftM (HashSpec.query input)
      let result ← counted (next output)
      return (result.1, Multiplicative.ofAdd (1 + Multiplicative.toAdd result.2))) := by
  simp [counted, simulateQ_bind, QueryImpl.withUnitCost,
    QueryImpl.withAddCost, QueryImpl.withCost, WriterT.run_bind,
    bind_assoc, map_eq_bind_pure_comp]

/-- Counting the verification cost of a lifted hash-only computation is its unit-cost count,
placed in the `verification` coordinate. -/
theorem verificationCount_lift (computation : OracleComp HashSpec α) :
    countQueries verificationCost (OracleComp.liftComp computation OracleWorld) =
      OracleComp.liftComp ((fun result =>
        (result.1, Counts.single .verification (Multiplicative.toAdd result.2))) <$>
          counted computation) OracleWorld := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [countQueries_pure, counted_pure, Counts.single]
  | query_bind input next ih =>
    simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query, countQueries_bind]
    change (do
      let left ← countQueries verificationCost (liftM (OracleWorld.query (.inr input)))
      let right ← countQueries verificationCost (OracleComp.liftComp (next left.1) OracleWorld)
      return (right.1, left.2 + right.2)) = _
    rw [countQueries_query]
    simp only [ih, bind_assoc, pure_bind, counted_query_bind]
    simp [map_eq_bind_pure_comp,
      verificationCost, Security.hashCost, RandomOracleModel.hashCost,
      Counts.single, Pi.single_add, bind_assoc]
    rfl

/-- On a well-framed request with a parseable signature, a run of the verifier charges between
`569` and `3824` hashes to the `verification` coordinate. -/
theorem verification_count_bounds (pk : PublicKey) (request : Message) (wire : Bytes)
    (message : Bytes) (signature : Signature)
    (hframe : request.frame = some message) (hparse : Signature.fromBytes? wire = some signature)
    (cache : QueryCache HashSpec) (result : Bool × Counts)
    (hresult : result ∈ support
      ((simulateQ (RandomOracleModel.impl Bytes HashOutput)
        (countQueries verificationCost (Scheme.verify pk request wire))).run' cache)) :
    569 ≤ result.2 .verification ∧ result.2 .verification ≤ 3824 := by
  rw [verify_lift, verificationCount_lift] at hresult
  rw [RandomOracleModel.impl, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_map, StateT.run'_map', support_map, Set.mem_image] at hresult
  obtain ⟨trace, htrace, rfl⟩ := hresult
  simpa only [Counts.single, Pi.single_eq_same] using
    (verify_bounds pk request wire message signature hframe hparse).simulated
      randomOracle cache trace htrace

/-- An accepting run of the verifier charges between `569` and `3824` hashes to the
`verification` coordinate. -/
theorem verification_accepted_count_bounds (pk : PublicKey) (request : Message) (wire : Bytes)
    (cache : QueryCache HashSpec) (result : Bool × Counts)
    (hresult : result ∈ support
      ((simulateQ (RandomOracleModel.impl Bytes HashOutput)
        (countQueries verificationCost (Scheme.verify pk request wire))).run' cache))
    (haccept : result.1 = true) :
    569 ≤ result.2 .verification ∧ result.2 .verification ≤ 3824 := by
  cases hframe : request.frame with
  | none =>
    simp only [Scheme.verify, hframe, countQueries_pure, simulateQ_pure,
      StateT.run'_eq, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    contradiction
  | some message =>
    cases hparse : Signature.fromBytes? wire with
    | none =>
      simp only [Scheme.verify, hframe, hparse, countQueries_pure, simulateQ_pure,
        StateT.run'_eq, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      contradiction
    | some signature =>
      exact verification_count_bounds pk request wire message signature hframe hparse cache result
        hresult

/-- The concrete experiment cannot accept a final forgery with fewer than 569 charged hashes. -/
theorem accepted_outcome_work (adversary : Adversary) (outcome : Outcome)
    (houtcome : outcome ∈ support (Security.run adversary)) (haccept : outcome.verified = true) :
    569 ≤ outcome.counts.work := by
  unfold Security.run RandomOracleModel.run Security.experiment at houtcome
  rw [simulateQ_bind, StateT.run'_bind', mem_support_bind_iff] at houtcome
  obtain ⟨⟨⟨sk, pk⟩, keygenCache⟩, _hkeygen, hafterKeygen⟩ := houtcome
  dsimp only at hafterKeygen
  rw [simulateQ_bind, StateT.run'_bind', mem_support_bind_iff] at hafterKeygen
  obtain ⟨⟨⟨⟨forgery, adversaryCounts⟩, signed⟩, adversaryCache⟩, _hadversary, hafterAdversary⟩ :=
    hafterKeygen
  dsimp only at hafterAdversary
  rw [simulateQ_bind, StateT.run'_bind', mem_support_bind_iff] at hafterAdversary
  obtain ⟨⟨⟨verified, verifierCounts⟩, verifierCache⟩, hverifier, hpure⟩ := hafterAdversary
  dsimp only at hpure
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
    support_pure, Set.mem_singleton_iff] at hpure
  subst outcome
  have hverifier' : (verified, verifierCounts) ∈ support
      ((simulateQ (RandomOracleModel.impl Bytes HashOutput)
        (countQueries verificationCost (Scheme.verify pk forgery.message forgery.signature))).run'
          adversaryCache) := by
    rw [StateT.run'_eq, support_map, Set.mem_image]
    exact ⟨((verified, verifierCounts), verifierCache), hverifier, rfl⟩
  have hbound := (verification_accepted_count_bounds pk forgery.message forgery.signature
    adversaryCache (verified, verifierCounts) hverifier' haccept).1
  change 569 ≤ verifierCounts .verification at hbound
  change 569 ≤ (Multiplicative.toAdd adversaryCounts + verifierCounts).work
  simp only [Counts.work, Pi.add_apply]
  omega

end SlhDsaSecurity.VerificationBudget
