/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Statement.Game.QueryBudget

/-!
# Complete-game source budgets

Syntactic adversary hash and signing bounds, together with a universal verifier bound, control
all supported results of the actual counted experiment. Its key generation and signer-internal
hashes remain outside the selected work. Arbitrary initial caches, rejected requests, losing
outcomes and malformed forgeries obey the same pathwise bounds before probability-one transport.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Game

variable {Output PK SK α : Type}

/-- A pure result incurs no charge in any source coordinate. -/
theorem countQueries_pure (cost : (World Output).Domain → Counts) (x : α) :
    countQueries cost (pure x) = pure (x, 0) := by simp [countQueries]

/-- Counting a query adds its actual charge to the continuation count. -/
theorem countQueries_query_bind (cost : (World Output).Domain → Counts)
    (input : (World Output).Domain)
    (next : (World Output).Range input → OracleComp (World Output) α) :
    countQueries cost (liftM ((World Output).query input) >>= next) = do
      let answer ← query input
      let result ← countQueries cost (next answer)
      return (result.1, cost input + result.2) := by
  simp [countQueries, addCostOracle, QueryImpl.withAddCost, WriterT.run_bind,
    bind_assoc]

/-- A total syntactic query bound bounds a single-source hash counter on every response path.
Private samples contribute zero, and all other source coordinates remain zero. -/
theorem countQueries_single_bounds (kind : QueryKind) (program : OracleComp (World Output) α)
    {n : Nat} (hbound : IsTotalQueryBound program n) {z : α × Counts}
    (hz : z ∈ support (countQueries (fun input => Counts.single kind (hashCost input)) program)) :
    ∃ charged, charged ≤ n ∧ z.2 = Counts.single kind charged := by
  induction program using OracleComp.inductionOn generalizing n z with
  | pure value =>
    rw [countQueries_pure] at hz
    have heq := eq_of_mem_support_pure _ hz
    subst z
    exact ⟨0, Nat.zero_le _, by ext k; simp [Counts.single]⟩
  | query_bind input next ih =>
    rw [isTotalQueryBound_query_bind_iff] at hbound
    rw [countQueries_query_bind] at hz
    obtain ⟨answer, _, hanswer⟩ := mem_support_bind_peel _ _ hz
    obtain ⟨result, hresult, hret⟩ := mem_support_bind_peel _ _ hanswer
    have heq := eq_of_mem_support_pure _ hret
    subst z
    obtain ⟨charged, hcharged, heq⟩ := ih answer (hbound.2 answer) hresult
    have hcost : hashCost input ≤ 1 := by
      rcases input with _ | _ <;> simp [hashCost, RandomOracleModel.hashCost]
    refine ⟨hashCost input + charged, by omega, ?_⟩
    dsimp only
    rw [heq]
    ext k
    simp only [Pi.add_apply, Counts.single, Pi.single_apply]
    split_ifs <;> simp

/-- Erasing all-hash instrumentation recovers the exact original oracle program. -/
theorem fst_map_countAllHashes (program : OracleComp (World Output) α) :
    Prod.fst <$> countAllHashes program = program := by
  simp [countAllHashes, Functor.map_map]

/-- Every supported result of an all-hash-counted program projects to an original result. -/
theorem mem_support_of_mem_support_countAllHashes (program : OracleComp (World Output) α)
    {z : α × Nat} (hz : z ∈ support (countAllHashes program)) : z.1 ∈ support program := by
  rw [← fst_map_countAllHashes program, support_map]
  exact ⟨z, hz, rfl⟩

/-- The real adversary phase and final verifier obey their syntactic budgets on every outcome.
The signing log has one entry per request, including rejected requests; winning is not assumed. -/
theorem afterKeygen_bounds (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) (keys : SK × PK) {qh qs v : Nat}
    (hh : IsQueryBoundP (adversary.main keys.2)
      (SignatureAlg.IsHashQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qh)
    (hs : IsQueryBoundP (adversary.main keys.2)
      (SignatureAlg.IsSignQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qs)
    (hv : ∀ forgery : Forgery, IsTotalQueryBound
      (scheme.verify keys.2 forgery.message forgery.signature) v)
    {outcome : Outcome} (houtcome : outcome ∈ support (afterKeygen scheme adversary keys)) :
    outcome.counts .hash ≤ qh ∧ outcome.counts .signing ≤ qs ∧
      outcome.counts .verification ≤ v ∧ outcome.signed.length = outcome.counts .signing := by
  rw [afterKeygen_eq_runPhase] at houtcome
  obtain ⟨⟨⟨forgery, phaseCounts⟩, signed⟩, hphase, houtcome⟩ := mem_support_bind_peel _ _ houtcome
  obtain ⟨⟨verified, verifierCounts⟩, hverify, houtcome⟩ := mem_support_bind_peel _ _ houtcome
  have heq := eq_of_mem_support_pure _ houtcome
  subst outcome
  obtain ⟨hhash, hsign, hverifier, suffix, hlog, hlength⟩ :=
    runPhase_bounds scheme keys.1 (adversary.main keys.2) [] hh hs hphase
  obtain ⟨charged, hcharged, hcount⟩ := countQueries_single_bounds .verification
    (scheme.verify keys.2 forgery.message forgery.signature) (hv forgery) hverify
  dsimp only at hhash hsign hverifier hlog hlength hcount hcharged
  simp only [hcount, Pi.add_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Counts.single] using hhash
  · simpa [Counts.single] using hsign
  · simpa [Counts.single, hverifier] using hcharged
  · simpa [Counts.single, hlog] using hlength

/-- The actual source-counted experiment obeys the adversary and verifier budgets.
Key generation and signer-internal hashes are excluded by the exact `adversaryWork` selector. -/
theorem experimentBySource_bounds (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) {qh qs v : Nat}
    (hadv : ∀ pk, IsQueryBoundP (adversary.main pk)
      (SignatureAlg.IsHashQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qh ∧
      IsQueryBoundP (adversary.main pk)
        (SignatureAlg.IsSignQuery (hs := RandomOracleModel.HashSpec Bytes Output)
          (M := Message) (S := Option Bytes)) qs)
    (hv : ∀ pk (forgery : Forgery), IsTotalQueryBound
      (scheme.verify pk forgery.message forgery.signature) v)
    {result : Outcome × Unforgeability.QueryCounts}
    (hresult : result ∈ support (experimentBySource scheme adversary)) :
    result.2 .sign ≤ qs ∧
      (∑ kind ∈ adversaryWork, result.2 kind) ≤ qh + qs + v ∧
      result.1.signed.length = result.2 .sign := by
  unfold experimentBySource at hresult
  obtain ⟨⟨keys, keygenHashes⟩, _, hresult⟩ := mem_support_bind_peel _ _ hresult
  obtain ⟨⟨outcome, laterHashes⟩, hafter, hresult⟩ := mem_support_bind_peel _ _ hresult
  have heq := eq_of_mem_support_pure _ hresult
  subst result
  obtain ⟨hhash, hsign, hverifier, hlog⟩ := afterKeygen_bounds scheme adversary keys
    (hadv keys.2).1 (hadv keys.2).2 (hv keys.2)
    (mem_support_of_mem_support_countAllHashes _ hafter)
  dsimp only at hhash hsign hverifier hlog
  dsimp only
  rw [sum_adversaryWork_sourceCounts]
  exact ⟨hsign, by omega, hlog⟩

/-- The same selected-work and log bounds hold from every initial random-oracle cache.
Cache contents affect answers but do not suppress repeated-call charges. -/
theorem experimentBySource_bounds_cached [SampleableType Output]
    (scheme : ExternalScheme Output PK SK)
    (adversary : Adversary Output PK) {qh qs v : Nat}
    (hadv : ∀ pk, IsQueryBoundP (adversary.main pk)
      (SignatureAlg.IsHashQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qh ∧
      IsQueryBoundP (adversary.main pk)
        (SignatureAlg.IsSignQuery (hs := RandomOracleModel.HashSpec Bytes Output)
          (M := Message) (S := Option Bytes)) qs)
    (hv : ∀ pk (forgery : Forgery), IsTotalQueryBound
      (scheme.verify pk forgery.message forgery.signature) v)
    (cache : QueryCache (RandomOracleModel.HashSpec Bytes Output))
    {result : Outcome × Unforgeability.QueryCounts}
    (hresult : result ∈ support ((simulateQ (RandomOracleModel.impl Bytes Output)
      (experimentBySource scheme adversary)).run' cache)) :
    result.2 .sign ≤ qs ∧
      (∑ kind ∈ adversaryWork, result.2 kind) ≤ qh + qs + v ∧
      result.1.signed.length = result.2 .sign :=
  experimentBySource_bounds scheme adversary hadv hv
    (support_simulateQ_run'_subset (RandomOracleModel.impl Bytes Output) _ cache hresult)

/-- Every outcome of the actual empty-cache security game respects the selected work budget.
The bound includes losing outcomes and malformed forgeries. -/
theorem securityGame_bounds [SampleableType Output]
    (scheme : ExternalScheme Output PK SK) (adversary : Adversary Output PK) {qh qs v : Nat}
    (hadv : ∀ pk, IsQueryBoundP (adversary.main pk)
      (SignatureAlg.IsHashQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qh ∧
      IsQueryBoundP (adversary.main pk)
        (SignatureAlg.IsSignQuery (hs := RandomOracleModel.HashSpec Bytes Output)
          (M := Message) (S := Option Bytes)) qs)
    (hv : ∀ pk (forgery : Forgery), IsTotalQueryBound
      (scheme.verify pk forgery.message forgery.signature) v)
    {result : Bool × Unforgeability.QueryCounts}
    (hresult : result ∈ support ((securityGame scheme).experiment () adversary)) :
    result.2 .sign ≤ qs ∧ (∑ kind ∈ adversaryWork, result.2 kind) ≤ qh + qs + v := by
  change result ∈ support ((fun r => (decide (Wins r.1), r.2)) <$>
    RandomOracleModel.run (experimentBySource scheme adversary)) at hresult
  rw [support_map] at hresult
  obtain ⟨result, hresult, rfl⟩ := hresult
  exact (experimentBySource_bounds_cached scheme adversary hadv hv ∅ hresult).imp_right And.left

/-- Pathwise adversary and verifier bounds imply the actual almost-sure signing and work bounds. -/
theorem almostSure_bounds [SampleableType Output]
    (scheme : ExternalScheme Output PK SK) (adversary : Adversary Output PK) {qh qs v : Nat}
    (hadv : ∀ pk, IsQueryBoundP (adversary.main pk)
      (SignatureAlg.IsHashQuery (hs := RandomOracleModel.HashSpec Bytes Output)
        (M := Message) (S := Option Bytes)) qh ∧
      IsQueryBoundP (adversary.main pk)
        (SignatureAlg.IsSignQuery (hs := RandomOracleModel.HashSpec Bytes Output)
          (M := Message) (S := Option Bytes)) qs)
    (hv : ∀ pk (forgery : Forgery), IsTotalQueryBound
      (scheme.verify pk forgery.message forgery.signature) v) :
    (qs ≤ signingLimit → WithinSigningLimit scheme adversary) ∧
      (securityGame scheme).HasQueryBound () adversaryWork adversary (qh + qs + v) := by
  constructor
  · intro hlimit
    exact prEvent_eq_one_of_forall_mem_support _ _ fun result hresult =>
      ((securityGame_bounds scheme adversary hadv hv hresult).1).trans hlimit
  · exact prEvent_eq_one_of_forall_mem_support _ _ fun result hresult =>
      (securityGame_bounds scheme adversary hadv hv hresult).2

end SLHDSA.SHAKE128s.Game
