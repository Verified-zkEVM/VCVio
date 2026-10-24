/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.BySourceShared
public import HashSig.SLHDSA.SHAKE128s.Proof.VerifierTally

/-!
# The joint cap's two hypotheses, from the budget

`ShareJoint.prEvent_realFlat_le` compares the flattened real game with the jointly capped one
under two hypotheses. Both follow from `BySourceBridge.TailBudgetW` at a drawn table, with the
adversary capped at `q - 569`:

* on every path, the adversary's weight plus the verifier's count is at most `q`
  (`cost_add_verification_le`): the pair of a real-phase point and a verifier point is a
  linked-run point, hence a warmed-tail point, where the budget applies;
* an accepted verification counts at least `569` (`VerifierTally.accepted_ge`), so its
  adversary stayed within `q - 569` (`accepted_le`);
* a parsed verification's charged cost plus `239` is at most its count
  (`VerifierTally.verifyCost_add_le`), and an unparsed one costs nothing, so the verifier stays
  within what the adversary left plus `330` (`verify_le`).
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.JointBudget

open Security CanonicalGraph WarmedGame WalkTable TableTail RecordedQueries RecordedPhase
  SharePresent ShareRealCap BySourceBridge

attribute [local irreducible] WarmedGame.afterSeeds Scheme.verify Scheme.keygenInternal
  Security.countQueries

/-- **On every path, the adversary's weight and the verifier's count are within the budget.** -/
theorem cost_add_verification_le {adversary : Adversary} {q : Nat}
    (hbudget : TailBudgetW adversary q) (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    ∀ z ∈ support (ShareJoint.advRun adversary (keysOf prfSeed publicSeed table)
        (walkOfTable prfSeed publicSeed table).2),
      ∀ w ∈ support (ShareJoint.verRun (keysOf prfSeed publicSeed table) z),
        realCost z.2 + (Multiplicative.toAdd w.2.1).1 .verification ≤ q := by
  intro z hz w hw
  have hr : ((((z.1, z.2.1), (w.1, Multiplicative.toAdd w.2.1)), z.2.2.1), w.2.2) ∈
      support (linkedRun adversary prfSeed publicSeed table) := by
    rw [linkedRun_eq, realFlat, mem_support_bind_iff]
    refine ⟨z, hz, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨w, hw, by simp⟩
  obtain ⟨result, hresult, houtcome, -⟩ :=
    exists_recordedTail_of_linked adversary prfSeed publicSeed table _ hr
  have htail : ((result.1.1.1, result.1.2), result.2) ∈
      support (WarmedGame.tail adversary (walkOfTable prfSeed publicSeed table)) := by
    rw [RecordedTail.tail_eq_map_recordedTail, support_map]
    exact ⟨result, hresult, rfl⟩
  have htotal := (hbudget _ (mem_support_graphWalk_walkOfTable prfSeed publicSeed table) _
    htail).2
  have hlength := SigningFaithful.signed_length_le_signing_tail adversary htail
  have hcounts : result.1.1.1.counts =
      (Multiplicative.toAdd z.2.1).1 + (Multiplicative.toAdd w.2.1).1 := by
    rw [houtcome]
    rfl
  have hsigned : result.1.1.1.signed = z.2.2.1 := by
    rw [houtcome]
    rfl
  have hserved := BySourceShared.servedCount_le_length z.2.2.1
  simp only [hcounts, hsigned, AdversaryQueries.work_add] at htotal hlength
  simp only [Pi.add_apply] at htotal hlength
  unfold realCost
  unfold Counts.work at htotal ⊢
  omega

/-- **An accepted forgery's adversary stays within `q - 569`.** -/
theorem accepted_le {adversary : Adversary} {q : Nat}
    (hbudget : TailBudgetW adversary q) (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    ∀ z ∈ support (ShareJoint.advRun adversary (keysOf prfSeed publicSeed table)
        (walkOfTable prfSeed publicSeed table).2),
      ∀ w ∈ support (ShareJoint.verRun (keysOf prfSeed publicSeed table) z),
        w.1 = true → realCost z.2 ≤ q - 569 := by
  intro z hz w hw haccept
  have h := cost_add_verification_le hbudget prfSeed publicSeed table z hz w hw
  have h569 := VerifierTally.accepted_ge _ _ _ _ w hw haccept
  omega

/-- **Within the cap, the verifier's charged cost is within what the adversary left, plus the
allowance.** -/
theorem verify_le {adversary : Adversary} {q : Nat}
    (hbudget : TailBudgetW adversary q) (prfSeed publicSeed : Digest) (table : Cells × Padding) :
    ∀ z ∈ support (ShareJoint.advRun adversary (keysOf prfSeed publicSeed table)
        (walkOfTable prfSeed publicSeed table).2),
      realCost z.2 ≤ q - 569 →
      ∀ w ∈ support (ShareJoint.verRun (keysOf prfSeed publicSeed table) z),
        ShareJoint.verifyCost (keysOf prfSeed publicSeed table).2.seed w.2 ≤
          (q - 569 - realCost z.2) + ShareJoint.verifierAllowance := by
  intro z hz hcost w hw
  unfold ShareJoint.verifierAllowance
  cases hframe : z.1.message.frame with
  | none =>
    rw [VerifierTally.verifyCost_eq_zero _ _ _ _ (Or.inl hframe) w hw]
    omega
  | some message =>
    cases hparse : Signature.fromBytes? z.1.signature with
    | none =>
      rw [VerifierTally.verifyCost_eq_zero _ _ _ _ (Or.inr hparse) w hw]
      omega
    | some signature =>
      have h := cost_add_verification_le hbudget prfSeed publicSeed table z hz w hw
      have hle := VerifierTally.verifyCost_add_le _ _ _ _ message signature hframe hparse w hw
      omega

/-- **At a drawn table, an event of the real game with an accepted forgery is at most as likely
in the game capped jointly at `q - 569`.** -/
theorem prEvent_realFlat_le {adversary : Adversary} {q : Nat}
    (hbudget : TailBudgetW adversary q) (prfSeed publicSeed : Digest) (table : Cells × Padding)
    (event : (((Forgery × Multiplicative Tally) × (Bool × Tally)) × SigningLog) ×
      QueryCache HashSpec → Prop) :
    Pr{let r ← (realFlat adversary (keysOf prfSeed publicSeed table)
          (walkOfTable prfSeed publicSeed table).2)}[event r ∧ r.1.1.2.1 = true] ≤
      Pr{let x ← (ShareJoint.realFlatJ adversary (q - 569) (keysOf prfSeed publicSeed table)
        (walkOfTable prfSeed publicSeed table).2)}[event x] :=
  ShareJoint.prEvent_realFlat_le adversary (q - 569) _ _ event
    (accepted_le hbudget prfSeed publicSeed table) (verify_le hbudget prfSeed publicSeed table)

end SLHDSA.SHAKE128s.JointBudget
