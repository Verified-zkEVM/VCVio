/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareJointCouple
public import HashSig.SLHDSA.SHAKE128s.Proof.ClaimsQueried
public import HashSig.SLHDSA.SHAKE128s.Proof.ShareFiled

/-!
# The jointly capped blind game files few charged entries

`ShareBound.blind_bound_of` charges a game at the number of entries its blind runs file that the
charge pays for (`ShareBound.charged`). For the jointly capped game that number is at most
`limit + verifierAllowance + 231`, on every blind run:

* the adversary's phase files at most what its cap spent, `limit - rem`
  (`CapRem.cost_capCompRem_le` with `ShareFlag.reportsCost`);
* the verifier files charged entries worth at most its own cap, `rem + verifierAllowance`
  (`CapRem.cost_capCompOpt_le`, the charged count growing by `chargedWeight` per query);
* the claims file only candidates not already filed, and a claim the verifier itself queried
  *was* filed, at the same stamp — so at most the `231` claims the verifier does not query
  (`ClaimsQueried.card_unqueried_claims_le`).

The third point needs the blind verifier's probes to be filed whatever happened before; it is
taken here as a hypothesis, `hfiled`, in the form the blind handler provides it.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.ShareJointBound

open Security CanonicalGraph ShareGame ShareFlag ShareBound ShareBlindFacts ShareJoint CapRem

/-! ## The charged count -/

/-- Filing one more input adds its own charge to the charged count. -/
theorem charged_append_single (publicSeed : Digest) (record : List (Bytes × List HashOutput))
    (input : Bytes) (served : List HashOutput) :
    charged publicSeed (record ++ [(input, served)]) =
      charged publicSeed record + chargedOf publicSeed input := by
  classical
  unfold charged chargedOf
  simp only [List.countP_append, List.countP_singleton]
  by_cases hlocate : ((GraphStakes.stakes publicSeed).locate input).isSome <;>
    by_cases hprefixed : Target127.SeedPrefixed publicSeed input <;>
      simp [hlocate, hprefixed] <;> omega

/-- Filing further inputs adds at most their number to the charged count. -/
theorem charged_append_le (publicSeed : Digest) (record extra : List (Bytes × List HashOutput)) :
    charged publicSeed (record ++ extra) ≤ charged publicSeed record + extra.length := by
  classical
  have h := charged_le_length publicSeed extra
  unfold charged at h ⊢
  simp only [List.countP_append]
  omega

/-- **A world step of a shared handler files exactly its hash input.** -/
theorem record_world_step (lenient : Bool) (setup : Setup) (queried : OracleWorld.Domain)
    (p : St × Bool) (z : OracleWorld.Range queried × (St × Bool))
    (hz : z ∈ support (((worldImpl lenient setup) queried).run p)) :
    z.2.1.record = p.1.record ++ (match queried with
      | Sum.inl _ => []
      | Sum.inr input => [(input, p.1.served)]) := by
  classical
  rw [ShareFiled.worldImpl_run] at hz
  rcases queried with coin | input
  · have hrun : ((handler lenient setup) (worldQuery (Sum.inl coin))).run p =
        (do
          let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
          pure (value, p)) := rfl
    rw [hrun] at hz
    erw [mem_support_bind_iff] at hz
    obtain ⟨value, -, hz⟩ := hz
    erw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp
  · have hrun : ((handler lenient setup) (worldQuery (Sum.inr input))).run p =
        (do
          let step ← route lenient setup p.1 input
          pure (step.1, ({ step.2 with record := p.1.record ++ [(input, p.1.served)] },
            p.2 || decide (¬ setup.Good ∨ Guess setup p.1.served input)))) := rfl
    rw [hrun] at hz
    erw [mem_support_bind_iff] at hz
    obtain ⟨step, -, hz⟩ := hz
    erw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    rfl

/-- **The charged count reports the verifier's charged weight.** -/
theorem reportsCost_charged (lenient : Bool) (setup : Setup) :
    CapComp.ReportsCost (worldImpl lenient setup) (chargedWeight setup.pk.seed)
      (fun p : St × Bool => charged setup.publicSeed p.1.record) := by
  intro queried p z hz
  change charged setup.publicSeed z.2.1.record = charged setup.publicSeed p.1.record + _
  rw [record_world_step lenient setup queried p z hz]
  rcases queried with coin | input
  · simp [chargedWeight]
  · exact charged_append_single setup.publicSeed p.1.record input p.1.served

/-! ## The bound -/

/-- **What the blind verifier's filing provides**: at any state, a run of the verifier keeps the
stamp, and every input the replayed verifier consults at the run's visible cache is filed at it. -/
@[expose] def VerifierFiles (setup : Setup) : Prop :=
  ∀ (request : Message) (wire : Bytes) (p : St × Bool) (w : Bool × (St × Bool)),
    w ∈ support ((simulateQ (worldImpl false setup)
      (Scheme.verify (m := OracleComp OracleWorld) setup.pk request wire)).run p) →
    w.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup w.2.1)
        (Scheme.verify (m := OracleComp HashSpec) setup.pk request wire) probe →
        (probe, p.1.served) ∈ w.2.1.record

/-- **The claims that are not already filed are among those the verifier does not query.** -/
theorem length_unfiled_claims_le (setup : Setup) (state : St) (forgery : Forgery)
    (hfiled : ∀ probe, ∀ message parsed, forgery.message.frame = some message →
      Signature.fromBytes? forgery.signature = some parsed →
      CacheReplay.QueriesUnder (visible setup state)
        (Scheme.verify (m := OracleComp HashSpec) setup.pk forgery.message forgery.signature)
        probe → (probe, state.served) ∈ state.record) :
    (unfiled state.record state.served (claimsOf setup state forgery)).length ≤ 231 := by
  classical
  unfold claimsOf
  split
  · rename_i message parsed hframe hparsed
    refine le_trans ?_ (ClaimsQueried.card_unqueried_claims_le (visible setup state) setup.pk
      forgery.message forgery.signature message parsed hframe hparsed)
    unfold unfiled
    refine (List.monotone_filter_right _ fun candidate hcandidate => ?_).length_le
    simp only [decide_eq_true_eq] at hcandidate ⊢
    exact fun hqueried => hcandidate (hfiled candidate message parsed hframe hparsed hqueried)
  · simp [unfiled]

/-- **The jointly capped game's filing runs file at most `limit + verifierAllowance + 231`
charged entries.** -/
theorem charged_filing_shareCompJ (setup : Setup) (hfiles : VerifierFiles setup)
    (adversary : Adversary) (limit : Nat) (flag : Bool) :
    ∀ z ∈ support ((simulateQ (filing setup) (shareCompJ adversary limit setup.pk)).run
        (St.start, flag)),
      charged setup.publicSeed z.2.1.record ≤ limit + verifierAllowance + 231 := by
  intro z hz
  unfold shareCompJ at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨a, ha, hz⟩ := hz
  rw [← QueryImpl.simulateQ_compose,
    compose_splitter_of (filing setup) false setup (filing_inl setup)] at ha
  have hcap := cost_capCompRem_le (advImpl false setup) weight
    (fun state : St × Bool => state.1.record.length) (reportsCost false setup)
    fallbackForgery (adversary.main setup.pk) limit (St.start, flag) a ha
  simp only [St.start, List.length_nil, Nat.zero_add] at hcap
  have hchargedA := charged_le_length setup.publicSeed a.2.1.record
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨v, hv, hz⟩ := hz
  rw [toShare, ← QueryImpl.simulateQ_compose (filing setup) (fun world =>
      (query (spec := ShareSpec) (worldQuery world) :
        OracleComp ShareSpec (OracleWorld.Range world))),
    compose_world_of (filing setup) false setup (filing_inl setup)] at hv
  have hverify := cost_capCompOpt_le (worldImpl false setup) (chargedWeight setup.pk.seed)
    (fun p : St × Bool => charged setup.publicSeed p.1.record) (reportsCost_charged false setup)
    _ (a.1.2 + verifierAllowance) a.2 v hv
  obtain ⟨result, state⟩ := v
  cases result with
  | none =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    simp only at hverify ⊢
    omega
  | some verified =>
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
      HasQuery.instOfMonadLift_query] at hz
    obtain ⟨claims, hclaims, hz⟩ := hz
    erw [simulateQ_spec_query] at hclaims
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    rw [filing_run, support_map] at hclaims
    obtain ⟨inner, hinner, rfl⟩ := hclaims
    have hrecord := (record_claims false setup a.1.1 (state.1, false) inner hinner).1 rfl
    simp only at hrecord ⊢
    rw [hrecord]
    -- the verifier's own probes were filed, at the stamp the claims are filed at
    have hrun := mem_support_of_capCompOpt_some (worldImpl false setup)
      (chargedWeight setup.pk.seed) _ _ a.2 verified state hv
    obtain ⟨hserved, hprobes⟩ := hfiles a.1.1.message a.1.1.signature a.2 (verified, state) hrun
    have hunfiled := length_unfiled_claims_le setup state.1 a.1.1
      fun probe _ _ _ _ hqueried => by
        have h := hprobes probe hqueried
        simp only at hserved h
        rw [hserved]
        exact h
    have happend := charged_append_le setup.publicSeed state.1.record
      (filed state.1.served (unfiled state.1.record state.1.served (claimsOf setup state.1 a.1.1)))
    have hlen : (filed state.1.served
        (unfiled state.1.record state.1.served (claimsOf setup state.1 a.1.1))).length =
        (unfiled state.1.record state.1.served (claimsOf setup state.1 a.1.1)).length := by
      simp [filed]
    simp only at hverify
    omega

/-- **And so its blind runs.** -/
theorem charged_blindRun_shareCompJ (setup : Setup) (hfiles : VerifierFiles setup)
    (adversary : Adversary) (limit : Nat) :
    ∀ z ∈ support (blindRun (shareCompJ adversary limit) setup),
      charged setup.publicSeed z.2.record ≤ limit + verifierAllowance + 231 := by
  intro z hz
  rw [← map_filingRun, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact charged_filing_shareCompJ setup hfiles adversary limit false w hw

end SLHDSA.SHAKE128s.ShareJointBound
