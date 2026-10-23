/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareJoint
public import HashSig.SLHDSA.SHAKE128s.Proof.ShareWhole

/-!
# The jointly capped games, coupled

`ShareWhole.couple_whole` couples the capped real game with the lenient game phase by phase,
from the step couplings `ShareCouple.couple_adv` and `couple_verify`. Those are couplings of
*handlers*, so they couple any computation run under them — in particular the jointly capped
phases of `ShareJoint`, which differ from the old ones only in the computation each phase runs.
What changes is the end: when the verifier's cap fires the lenient game skips the claims, and the
real game reports a rejection. So the claims clause of the final relation is kept only for an
accepted forgery, together with the real verifier's uncapped run that accepted it, which is what
the input-side event reads.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace SlhDsaSecurity.ShareJointCouple

variable {α : Type}

open Security CanonicalGraph ShareGame ShareCouple ShareInv ShareWhole ShareJoint CapRem

/-! ## The lenient game, phase by phase -/

theorem toShare_run (lenient : Bool) (setup : Setup) {α : Type}
    (computation : OracleComp OracleWorld α) (p : St × Bool) :
    (simulateQ (handler lenient setup) (toShare computation)).run p =
      (simulateQ (ShareBound.worldImpl lenient setup) computation).run p := by
  rw [toShare, QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := ShareBound.worldImpl lenient setup)
    (fun _ => rfl)]

set_option maxHeartbeats 1000000 in
/-- **The jointly capped lenient game is its adversary's phase, then the capped verifier, then
the claims if the verifier finished.** -/
theorem lenient_eq (setup : Setup) (adversary : Adversary) (limit : Nat) :
    (simulateQ (handler true setup) (shareCompJ adversary limit setup.pk)).run (St.start, false) =
      (simulateQ (ShareFlag.advImpl true setup) (capCompRem weight fallbackForgery limit
          (adversary.main setup.pk))).run (St.start, false) >>= fun a =>
        (simulateQ (ShareBound.worldImpl true setup)
            (cappedVerify setup.pk (a.1.2 + verifierAllowance) a.1.1)).run a.2 >>= fun v =>
          (match v.1 with
            | none => pure ((a.1.1, false), v.2)
            | some verified => pure ((a.1.1, verified), claimsStep setup v.2 a.1.1) :
            ProbComp ((Forgery × Bool) × (St × Bool))) := by
  unfold shareCompJ
  rw [simulateQ_bind, StateT.run_bind, ← QueryImpl.simulateQ_compose]
  refine bind_congr fun a => ?_
  rw [simulateQ_bind, StateT.run_bind, toShare_run]
  refine bind_congr fun v => ?_
  obtain ⟨result, state⟩ := v
  cases result with
  | none => simp
  | some verified =>
    simp only [simulateQ_bind, StateT.run_bind, HasQuery.instOfMonadLift_query]
    erw [simulateQ_spec_query]
    rw [handler_claims_run]
    simp

/-! ## The coupling -/

/-- **What the jointly capped coupling's two ends share.** Forgery and verdict agree; the real
cache and log are the lenient state's; every recorded input is filed; and an accepted forgery's
claims were taken, with the real verifier's uncapped run that accepted it. -/
def FinalJ (setup : Setup)
    (real : (((Forgery × Multiplicative RecordedQueries.Tally) × (Bool × RecordedQueries.Tally)) ×
      SigningLog) × QueryCache HashSpec)
    (lenient : (Forgery × Bool) × (St × Bool)) : Prop :=
  lenient.1.1 = real.1.1.1.1 ∧ lenient.1.2 = real.1.1.2.1 ∧
    ∃ stateV : St × Bool, Inv setup stateV ∧
      real.2 = realView setup stateV.1 ∧ real.1.2 = stateV.1.log ∧
      (∀ input ∈ (Multiplicative.toAdd real.1.1.1.2).2,
        ∃ entry ∈ stateV.1.record, entry.1 = input) ∧
      (∀ input ∈ real.1.1.2.2.2,
        ∃ entry ∈ stateV.1.record, entry.1 = input ∧ entry.2 = stateV.1.served) ∧
      (real.1.1.2.1 = true →
        lenient.2 = claimsStep setup stateV lenient.1.1 ∧
          ∃ (zs : SharePresent.RealState) (w : Bool × SharePresent.VerifyState),
            w ∈ support ((simulateQ SharePresent.realWorldImpl
              (Scheme.verify (m := OracleComp OracleWorld) setup.pk real.1.1.1.1.message
                real.1.1.1.1.signature)).run (1, zs.2.2)) ∧
            real = ((((real.1.1.1.1, zs.1), (w.1, Multiplicative.toAdd w.2.1)), zs.2.1), w.2.2))

set_option maxHeartbeats 2000000 in
/-- **The jointly capped real game and the jointly capped lenient game, coupled.** -/
theorem couple_whole (setup : Setup) (hgood : setup.Good) (adversary : Adversary) (limit : Nat) :
    RelTriple (realFlatJ adversary limit (setup.sk, setup.pk) setup.warm)
      ((simulateQ (handler true setup) (shareCompJ adversary limit setup.pk)).run (St.start, false))
      (FinalJ setup) := by
  rw [realFlatJ, lenient_eq]
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
  refine relTriple_bind (relTriple_support_left (relTriple_support_right (relTriple_simulateQ_run
    SharePresent.realWorldImpl (ShareBound.worldImpl true setup)
    (RelV setup a.2.1.log a.2.1.served (Multiplicative.toAdd z.2.1).2) _
    (couple_verify setup a.2.1.log a.2.1.served (Multiplicative.toAdd z.2.1).2) (1, z.2.2.2) a.2
    hstartV))) fun w v hwv => ?_
  obtain ⟨⟨⟨hverified, hrelv⟩, hv⟩, hw⟩ := hwv
  have hinvV : Inv setup v.2 := SignedWatch.run_invariant (ShareBound.worldImpl true setup)
    (Inv setup) (inv_verify setup) _ a.2 hinvA v hv
  have hlog : z.2.2.1 = v.2.1.log := by rw [hrel.log, hrelv.logEq]
  have hver : ∀ x ∈ (Multiplicative.toAdd w.2.1).2,
      ∃ entry ∈ v.2.1.record, entry.1 = x ∧ entry.2 = v.2.1.served := by
    intro x hx
    obtain ⟨entry, hentry, hx, hsnap⟩ := hrelv.verifier x hx
    exact ⟨entry, hentry, hx, hsnap.trans hrelv.servedEq.symm⟩
  obtain ⟨result, state⟩ := v
  obtain ⟨wResult, wState⟩ := w
  dsimp only at hverified hrelv hinvV hlog hver hw ⊢
  subst hverified
  cases wResult with
  | none =>
    refine relTriple_pure_pure ⟨rfl, rfl, state, hinvV, hrelv.cache, hlog, hrelv.adversary, hver,
      fun h => absurd h (by simp)⟩
  | some verified =>
    refine relTriple_pure_pure ⟨rfl, rfl, state, hinvV, hrelv.cache, hlog, hrelv.adversary, hver,
      fun _ => ⟨rfl, z.2, (verified, wState), ?_, rfl⟩⟩
    exact mem_support_of_capCompOpt_some SharePresent.realWorldImpl
      (chargedWeight setup.pk.seed) _ _ (1, z.2.2.2) verified wState hw

end SlhDsaSecurity.ShareJointCouple
