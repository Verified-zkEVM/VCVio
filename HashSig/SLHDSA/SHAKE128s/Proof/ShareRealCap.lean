/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SharePresent
public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenCost
public import HashSig.SLHDSA.SHAKE128s.Proof.WarmedCharges

/-!
# The cap in the real game

The shared games run the adversary capped at a number of weighted queries (`capAdv`). The
flattened real handler reports the cap's weight in its own state (`reportsCost_real`): the
adversary's work, plus one per served request (`realCost`). `answer_isSome` says the stripped
signer answers exactly the framed requests, and `exists_recordedTail_of_linked` relates a point
the linked run reaches to one the recorded tail reaches.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareRealCap

open Security CanonicalGraph WarmedGame WalkTable TableTail RecordedQueries RecordedPhase
  SharePresent

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

/-! ## The stripped signer answers exactly the framed requests -/

theorem answer_isSome (warm : QueryCache HashSpec) (sk : SecretKey) (request : Message)
    (cache : QueryCache HashSpec) (z : Option Bytes × QueryCache HashSpec)
    (hz : z ∈ support ((simulateQ KeygenUniform.rom
      (StrippedGame.strippedSign warm sk request)).run cache)) :
    z.1.isSome = request.frame.isSome := by
  unfold StrippedGame.strippedSign Scheme.sign at hz
  cases hframe : request.frame with
  | none =>
    simp only [hframe] at hz
    simp only [simulateQ_pure, OracleComp.liftComp_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
  | some message =>
    simp only [hframe] at hz
    simp only [bind_pure_comp, simulateQ_map, OracleComp.liftComp_map, StateT.run_map,
      support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    rfl

/-! ## The real handler reports the cap's weight -/

theorem exists_of_mem_support_map {α β : Type} (f : α → β) (mx : ProbComp α) (z : β)
    (hz : z ∈ support (f <$> mx)) : ∃ w ∈ support mx, f w = z := by
  rw [support_map] at hz
  exact hz

/-- The cap's weight, read off the flattened real state. -/
def realCost (state : RealState) : Nat :=
  (Multiplicative.toAdd state.1).1.work + AdversaryQueries.servedCount state.2.1

theorem reportsCost_real (warm : QueryCache HashSpec) (sk : SecretKey) :
    CapComp.ReportsCost (realImpl (StrippedGame.strippedSign warm sk)) ShareGame.weight
      realCost := by
  intro queried state z hz
  rcases queried with world | request
  · rw [realImpl_world_run] at hz
    obtain ⟨w, -, rfl⟩ := exists_of_mem_support_map _ _ _ hz
    rcases world with coin | input
    · simp [realCost, phaseCost, ShareGame.weight, AdversaryQueries.work_add,
        AdversaryQueries.work_single_hash, hashCost, Xmss.RandomOracleModel.hashCost]
    · simp [realCost, phaseCost, ShareGame.weight, AdversaryQueries.work_add,
        AdversaryQueries.work_single_hash, hashCost, Xmss.RandomOracleModel.hashCost]
      omega
  · rw [realImpl_request_run] at hz
    obtain ⟨w, hw, rfl⟩ := exists_of_mem_support_map _ _ _ hz
    have hsome := answer_isSome warm sk request state.2.2 w hw
    simp only [realCost, phaseCost, ShareGame.weight, toAdd_mul, toAdd_ofAdd, Prod.fst_add,
      AdversaryQueries.work_add, AdversaryQueries.work_single_signing,
      AdversaryQueries.servedCount_append, hsome]
    omega

/-! ## The capped adversary -/

/-- The adversary, capped at `limit` weighted queries. -/
noncomputable def capAdv (adversary : Adversary) (limit : Nat) : Adversary :=
  ⟨fun pk => CapComp.capComp ShareGame.weight ShareGame.fallbackForgery limit (adversary.main pk)⟩

/-! ## The linked run and the recorded tail -/

/-- A point the linked run reaches is one the recorded tail reaches, with its count beside it. -/
theorem exists_recordedTail_of_linked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : Cells × Padding)
    (r : ((((Forgery × Multiplicative Tally) × (Bool × Tally)) × SigningLog) ×
      QueryCache HashSpec))
    (hr : r ∈ support (linkedRun adversary prfSeed publicSeed table)) :
    ∃ result ∈ support (RecordedTail.recordedTail adversary (walkOfTable prfSeed publicSeed table)),
      result.1.1 = LinkedGame.outcomeOf r.1 ∧ result.2 = r.2 := by
  classical
  have hpos : Pr{let result ← linkedRun adversary prfSeed publicSeed table}[(LinkedGame.outcomeOf result.1, result.2) =
      (LinkedGame.outcomeOf r.1, r.2)] ≠ 0 :=
    probEvent_ne_zero_iff.mpr ⟨r, hr, rfl⟩
  rw [← probEvent_recordedTail_linked adversary prfSeed publicSeed table
    (fun x => x = (LinkedGame.outcomeOf r.1, r.2))] at hpos
  obtain ⟨result, hresult, heq⟩ := probEvent_ne_zero_iff.mp hpos
  exact ⟨result, hresult, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

end SlhDsaSecurity.ShareRealCap
