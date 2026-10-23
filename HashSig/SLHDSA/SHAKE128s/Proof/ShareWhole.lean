/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareInv

/-!
# The whole real game against the whole lenient game

The step couplings of `ShareCouple` lift to the two phases by `relTriple_simulateQ_run`, and the
phases bind into one coupling of the capped real game with the lenient game at the same setup.
What the coupling's postcondition carries is what the event needs: the forgeries agree, the real
cache is the view of the lenient state, the logs agree, every input the real game recorded is
filed in the lenient record (the verifier's at the final digests), and the lenient state keeps
its invariant.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace SlhDsaSecurity.ShareWhole

variable {α β : Type}

open Security CanonicalGraph ShareGame ShareCouple ShareInv

/-! ## Couplings that remember where they came from -/

variable {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  [OracleSpec.AnswerMeasure spec₁] [OracleSpec.AnswerMeasure spec₂]
  [∀ t, Finite (spec₁.Range t)] [∀ t, Finite (spec₂.Range t)] {α β : Type}

/-- **A coupling's right side lies in the right computation's support.** -/
theorem relTriple_support_right {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (h : RelTriple oa ob R) :
    RelTriple oa ob (fun a b => R a b ∧ b ∈ support ob) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at h ⊢
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  filter_upwards [hc, ae_mem_support_prod c] with z hz hmem
  exact ⟨hz, hmem.2⟩

/-- **A coupling's left side lies in the left computation's support.** -/
theorem relTriple_support_left {oa : OracleComp spec₁ α} {ob : OracleComp spec₂ β}
    {R : RelPost α β} (h : RelTriple oa ob R) :
    RelTriple oa ob (fun a b => R a b ∧ a ∈ support oa) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at h ⊢
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  filter_upwards [hc, ae_mem_support_prod c] with z hz hmem
  exact ⟨hz, hmem.1⟩

/-! ## The lenient game, phase by phase -/

open scoped Classical in
/-- What the claims step leaves. -/
noncomputable def claimsStep (setup : Setup) (p : St × Bool) (forgery : Forgery) : St × Bool :=
  ({ p.1 with
      record := if p.2 then p.1.record else
        p.1.record ++ (unfiled p.1.record p.1.served (claimsOf setup p.1 forgery)).map
          (fun candidate => (candidate, p.1.served)) },
    p.2 || decide (¬ setup.Good ∨
      ∃ candidate ∈ claimsOf setup p.1 forgery, Guess setup p.1.served candidate))

theorem handler_claims_run (lenient : Bool) (setup : Setup) (forgery : Forgery) (p : St × Bool) :
    ((handler lenient setup) (Sum.inr forgery)).run p =
      (pure ((), claimsStep setup p forgery) : ProbComp (Unit × (St × Bool))) := rfl

set_option maxHeartbeats 1000000 in
/-- **The lenient game is its adversary's phase, then the verifier, then the claims.** -/
theorem lenient_eq (setup : Setup) (adversary : Adversary) (limit : Nat) :
    (simulateQ (handler true setup) (shareComp adversary limit setup.pk)).run (St.start, false) =
      (simulateQ (ShareFlag.advImpl true setup) (CapComp.capComp weight fallbackForgery limit
          (adversary.main setup.pk))).run (St.start, false) >>= fun a =>
        (simulateQ (ShareBound.worldImpl true setup)
            (Scheme.verify (m := OracleComp OracleWorld) setup.pk a.1.message a.1.signature)).run
            a.2 >>= fun v =>
          (pure ((a.1, v.1), claimsStep setup v.2 a.1) :
            ProbComp ((Forgery × Bool) × (St × Bool))) := by
  unfold shareComp
  rw [simulateQ_bind, StateT.run_bind, ← QueryImpl.simulateQ_compose]
  refine bind_congr fun a => ?_
  rw [simulateQ_bind, StateT.run_bind, ShareBound.verifyShare_run]
  refine bind_congr fun v => ?_
  simp only [simulateQ_bind, StateT.run_bind, HasQuery.instOfMonadLift_query]
  erw [simulateQ_spec_query]
  rw [handler_claims_run]
  simp

/-! ## The coupling -/

/-- **What the coupling's two ends share.** -/
def Final (setup : Setup)
    (real : (((Forgery × Multiplicative RecordedQueries.Tally) × (Bool × RecordedQueries.Tally)) ×
      SigningLog) × QueryCache HashSpec)
    (lenient : (Forgery × Bool) × (St × Bool)) : Prop :=
  lenient.1.1 = real.1.1.1.1 ∧
    ∃ stateV : St × Bool, Inv setup stateV ∧
      lenient.2 = claimsStep setup stateV lenient.1.1 ∧
      real.2 = realView setup stateV.1 ∧ real.1.2 = stateV.1.log ∧
      (∀ input ∈ (Multiplicative.toAdd real.1.1.1.2).2,
        ∃ entry ∈ stateV.1.record, entry.1 = input) ∧
      (∀ input ∈ real.1.1.2.2.2,
        ∃ entry ∈ stateV.1.record, entry.1 = input ∧ entry.2 = stateV.1.served)

theorem rel_start (setup : Setup) : Rel setup (1, [], setup.warm) (St.start, false) where
  cache := by
    refine QueryCache.ext fun input => ?_
    unfold realView merged St.start
    cases h : setup.warm input with
    | some a => simp [h]
    | none => simp [h]
  log := rfl
  record := by simp

set_option maxHeartbeats 2000000 in
/-- **The capped real game and the lenient game, coupled.** -/
theorem couple_whole (setup : Setup) (hgood : setup.Good) (adversary : Adversary) (limit : Nat) :
    RelTriple (SharePresent.realFlat (ShareRealCap.capAdv adversary limit) (setup.sk, setup.pk)
        setup.warm)
      ((simulateQ (handler true setup) (shareComp adversary limit setup.pk)).run (St.start, false))
      (Final setup) := by
  rw [SharePresent.realFlat, lenient_eq]
  refine relTriple_bind (relTriple_support_right (relTriple_simulateQ_run
    (SharePresent.realImpl (StrippedGame.strippedSign setup.warm setup.sk))
    (ShareFlag.advImpl true setup) (Rel setup) _ (couple_adv setup hgood) (1, [], setup.warm)
    (St.start, false) (rel_start setup))) fun z a hza => ?_
  obtain ⟨⟨hforgery, hrel⟩, ha⟩ := hza
  have hinvA : Inv setup a.2 := SignedWatch.run_invariant (ShareFlag.advImpl true setup)
    (Inv setup) (inv_adv setup hgood) _ (St.start, false) (inv_start setup) a ha
  have hstartV : RelV setup a.2.1.log a.2.1.served (Multiplicative.toAdd z.2.1).2 (1, z.2.2.2) a.2 :=
    ⟨hrel.cache, rfl, rfl, hrel.record, by simp⟩
  rw [hforgery]
  refine relTriple_bind (relTriple_support_right (relTriple_simulateQ_run
    SharePresent.realWorldImpl (ShareBound.worldImpl true setup)
    (RelV setup a.2.1.log a.2.1.served (Multiplicative.toAdd z.2.1).2) _
    (couple_verify setup a.2.1.log a.2.1.served (Multiplicative.toAdd z.2.1).2) (1, z.2.2.2) a.2
    hstartV)) fun w v hwv => ?_
  obtain ⟨⟨hverified, hrelv⟩, hv⟩ := hwv
  have hinvV : Inv setup v.2 := SignedWatch.run_invariant (ShareBound.worldImpl true setup)
    (Inv setup) (inv_verify setup) _ a.2 hinvA v hv
  refine relTriple_pure_pure ⟨rfl, v.2, hinvV, rfl, hrelv.cache, ?_, hrelv.adversary, ?_⟩
  · rw [hrel.log, hrelv.logEq]
  · intro x hx
    obtain ⟨entry, hentry, hx, hsnap⟩ := hrelv.verifier x hx
    exact ⟨entry, hentry, hx, hsnap.trans hrelv.servedEq.symm⟩

end SlhDsaSecurity.ShareWhole
