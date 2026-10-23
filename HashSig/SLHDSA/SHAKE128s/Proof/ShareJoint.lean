/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareRealCap
public import HashSig.SLHDSA.SHAKE128s.Proof.CapRem

/-!
# The shared games, capped jointly

`ShareGame.shareComp` caps the adversary at the budget left after key generation and runs the
verifier uncapped, paying for it with the constant `3929` — affordable only because key
generation's `18432` calls are in the budget. With key generation free, the verifier has to be
paid for at its own count, so it is capped too, against **what the adversary left**:

* the adversary is capped at `limit` weighted queries, and `CapRem.capCompRem` reports the
  remainder `rem`;
* the verifier is capped at `rem + verifierAllowance` on its **charged** queries
  (`chargedWeight`): those the shared charge pays for — a query locating a node, or one not
  prefixed by the public seed. Every parsed verification also makes at least `239` queries that
  are neither (`VerifyFree.verify_free`), and those are what the allowance spends;
* if the verifier's cap fires, the claims are skipped: nothing a real run does is lost, because
  the real verifier never exceeds its cap.

On the real side (`realFlatJ`) the same two caps are applied to the flattened real game, and
`probEvent_realFlat_le` says an event of the real game that comes with an accepted forgery is at
most as likely in the capped one: an accepted forgery's verifier makes at least `569` calls, so
its adversary stayed within `limit`, and its verifier within its own cap.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareJoint

variable {α : Type}

open Security CanonicalGraph ShareGame SharePresent RecordedQueries CapComp CapRem

/-! ## The weights -/

open scoped Classical in
/-- **A verifier query's weight**: one if the shared charge pays for its input. -/
noncomputable def chargedOf (publicSeed : Digest) (input : Bytes) : Nat :=
  (if ((GraphStakes.stakes publicSeed).locate input).isSome then 1 else 0) +
    if Target127.SeedPrefixed publicSeed input then 0 else 1

/-- The charged weight of a world query: coins are free. -/
noncomputable def chargedWeight (publicSeed : Digest) : OracleWorld.Domain → Nat
  | Sum.inl _ => 0
  | Sum.inr input => chargedOf publicSeed input

/-- What the verifier may spend beyond what the adversary left: the `569` calls an accepted
forgery's verification costs at least, less the `239` of them the charge never pays for. -/
def verifierAllowance : Nat := 330

/-! ## The two games -/

/-- A world computation, as queries of the shared games. -/
noncomputable def toShare {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp ShareSpec α :=
  simulateQ (fun world => (query (spec := ShareSpec) (worldQuery world) :
      OracleComp ShareSpec (OracleWorld.Range world))) computation

/-- The verifier, capped on its charged queries. -/
noncomputable def cappedVerify (pk : PublicKey) (limit : Nat) (forgery : Forgery) :
    OracleComp OracleWorld (Option Bool) :=
  capCompOpt (chargedWeight pk.seed) limit
    (Scheme.verify (m := OracleComp OracleWorld) pk forgery.message forgery.signature)

/-- **The computation both shared games run, capped jointly.** -/
noncomputable def shareCompJ (adversary : Adversary) (limit : Nat) (pk : PublicKey) :
    OracleComp ShareSpec (Forgery × Bool) := do
  let p ← simulateQ splitter
    (capCompRem weight fallbackForgery limit (adversary.main pk))
  let verified ← toShare (cappedVerify pk (p.2 + verifierAllowance) p.1)
  match verified with
  | none => pure (p.1, false)
  | some verified => do
      let _ ← (query (spec := ShareSpec) (Sum.inr p.1) : OracleComp ShareSpec Unit)
      pure (p.1, verified)

/-- **The real game at a drawn table, flattened and capped jointly.** -/
noncomputable def realFlatJ (adversary : Adversary) (limit : Nat) (keys : SecretKey × PublicKey)
    (warm : QueryCache HashSpec) :
    ProbComp ((((Forgery × Multiplicative Tally) × (Bool × Tally)) × SigningLog) ×
      QueryCache HashSpec) := do
  let z ← (simulateQ (realImpl (StrippedGame.strippedSign warm keys.1))
    (capCompRem weight fallbackForgery limit (adversary.main keys.2))).run (1, [], warm)
  let w ← (simulateQ realWorldImpl (cappedVerify keys.2 (z.1.2 + verifierAllowance) z.1.1)).run
    (1, z.2.2.2)
  pure ((((z.1.1, z.2.1), (w.1.getD false, Multiplicative.toAdd w.2.1)), z.2.2.1), w.2.2)

/-! ## The verifier's charged cost, read off its tally -/

/-- The charged cost of the verifier's tally: its recorded inputs, weighed. -/
noncomputable def verifyCost (publicSeed : Digest) (state : VerifyState) : Nat :=
  ((Multiplicative.toAdd state.1).2.map (chargedOf publicSeed)).sum

theorem reportsCost_verify (publicSeed : Digest) :
    ReportsCost realWorldImpl (chargedWeight publicSeed) (verifyCost publicSeed) := by
  intro queried state z hz
  rw [realWorldImpl_run] at hz
  obtain ⟨w, -, rfl⟩ := ShareRealCap.exists_of_mem_support_map _ _ _ hz
  rcases queried with coin | input
  · simp [verifyCost, verifierCost, recordOf, chargedWeight]
  · simp [verifyCost, verifierCost, recordOf, chargedWeight, Nat.add_comm]

theorem verifyCost_one (publicSeed : Digest) (cache : QueryCache HashSpec) :
    verifyCost publicSeed (1, cache) = 0 := by
  simp [verifyCost]

theorem realCost_start (warm : QueryCache HashSpec) : ShareRealCap.realCost (1, [], warm) = 0 := by
  simp [ShareRealCap.realCost, AdversaryQueries.servedCount, Counts.work]

/-! ## The real game, until the caps fire -/

/-- The real game's adversary phase. -/
noncomputable abbrev advRun (adversary : Adversary) (keys : SecretKey × PublicKey)
    (warm : QueryCache HashSpec) : ProbComp (Forgery × RealState) :=
  (simulateQ (realImpl (StrippedGame.strippedSign warm keys.1)) (adversary.main keys.2)).run
    (1, [], warm)

/-- The real game's verifier, after a phase. -/
noncomputable abbrev verRun (keys : SecretKey × PublicKey) (z : Forgery × RealState) :
    ProbComp (Bool × VerifyState) :=
  (simulateQ realWorldImpl
    (Scheme.verify (m := OracleComp OracleWorld) keys.2 z.1.message z.1.signature)).run
    (1, z.2.2.2)

/-- What both games return, from a phase and a verifier run. -/
def assemble (z : Forgery × RealState) (w : Bool × VerifyState) :
    (((Forgery × Multiplicative Tally) × (Bool × Tally)) × SigningLog) × QueryCache HashSpec :=
  ((((z.1, z.2.1), (w.1, Multiplicative.toAdd w.2.1)), z.2.2.1), w.2.2)

theorem realFlat_eq (adversary : Adversary) (keys : SecretKey × PublicKey)
    (warm : QueryCache HashSpec) :
    realFlat adversary keys warm =
      advRun adversary keys warm >>= fun z => verRun keys z >>= fun w => pure (assemble z w) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- **An event of the real game with an accepted forgery is at most as likely in the jointly
capped one**, given that an accepted forgery's adversary stays within `limit` and that, within
it, the verifier stays within its cap. -/
theorem probEvent_realFlat_le (adversary : Adversary) (limit : Nat)
    (keys : SecretKey × PublicKey) (warm : QueryCache HashSpec)
    (event : (((Forgery × Multiplicative Tally) × (Bool × Tally)) × SigningLog) ×
      QueryCache HashSpec → Prop)
    (haccepted : ∀ z ∈ support (advRun adversary keys warm), ∀ w ∈ support (verRun keys z),
      w.1 = true → ShareRealCap.realCost z.2 ≤ limit)
    (hverify : ∀ z ∈ support (advRun adversary keys warm), ShareRealCap.realCost z.2 ≤ limit →
      ∀ w ∈ support (verRun keys z),
        verifyCost keys.2.seed w.2 ≤ (limit - ShareRealCap.realCost z.2) + verifierAllowance) :
    Pr{let r ← realFlat adversary keys warm}[event r ∧ r.1.1.2.1 = true] ≤
      Pr{let x ← realFlatJ adversary limit keys warm}[event x] := by
  classical
  -- The capped verifier, after a phase whose remainder is read off.
  let capped : (Forgery × Nat) × RealState →
      ProbComp ((((Forgery × Multiplicative Tally) × (Bool × Tally)) × SigningLog) ×
        QueryCache HashSpec) := fun z =>
    (simulateQ realWorldImpl (cappedVerify keys.2 (z.1.2 + verifierAllowance) z.1.1)).run
      (1, z.2.2.2) >>= fun w =>
        pure ((((z.1.1, z.2.1), (w.1.getD false, Multiplicative.toAdd w.2.1)), z.2.2.1), w.2.2)
  have hJ : realFlatJ adversary limit keys warm =
      (simulateQ (realImpl (StrippedGame.strippedSign warm keys.1))
        (capCompRem weight fallbackForgery limit (adversary.main keys.2))).run (1, [], warm) >>=
        capped := rfl
  have hstep := probEvent_le_capCompRem (realImpl (StrippedGame.strippedSign warm keys.1)) weight
    ShareRealCap.realCost (ShareRealCap.reportsCost_real warm keys.1) fallbackForgery event
    (adversary.main keys.2) limit (1, [], warm) capped
  rw [hJ]
  refine le_trans ?_ hstep
  rw [realCost_start, Nat.zero_add, realFlat_eq]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun z hz => ?_
  rw [prEvent_map]
  by_cases hcost : ShareRealCap.realCost z.2 ≤ limit
  · -- within the cap, the capped verifier is the verifier
    have hlaw : (simulateQ realWorldImpl
          (cappedVerify keys.2 (limit - ShareRealCap.realCost z.2 + verifierAllowance) z.1)).run
          (1, z.2.2.2) =ᵈ
        (fun w => (some w.1, w.2)) <$> verRun keys z := by
      refine evalDist_capCompOpt realWorldImpl (chargedWeight keys.2.seed)
        (verifyCost keys.2.seed) (reportsCost_verify keys.2.seed)
        (fun _ _ => prFail_eq_zero _) _ _ (1, z.2.2.2) fun w hw => ?_
      rw [verifyCost_one, Nat.zero_add]
      exact hverify z hz hcost w hw
    have hbind : capped ((z.1, limit - ShareRealCap.realCost z.2), z.2) =ᵈ
        (verRun keys z >>= fun w => pure (assemble z w)) := by
      refine (hlaw.bind_left _).trans ?_
      rw [bind_map_left]
      rfl
    calc Pr{let r ← verRun keys z >>= fun w => pure (assemble z w)}[
            event r ∧ r.1.1.2.1 = true]
        ≤ Pr{let r ← verRun keys z >>= fun w => pure (assemble z w)}[event r] :=
          prEvent_mono _ _ _ fun r h => h.1
      _ = Pr{let r ← capped ((z.1, limit - ShareRealCap.realCost z.2), z.2)}[event r] :=
          (hbind.prEvent_eq event).symm
      _ = _ := prEvent_congr _ _ _ fun b => by simp [hcost]
  · -- beyond the cap the forgery is not accepted
    refine le_of_eq_of_le (b := 0) (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hev => ?_)
      zero_le
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    exact hcost (haccepted z hz w hw hev.2)

end SlhDsaSecurity.ShareJoint
