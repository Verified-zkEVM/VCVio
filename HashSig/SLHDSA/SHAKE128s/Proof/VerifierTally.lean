/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareJoint
public import HashSig.SLHDSA.SHAKE128s.Proof.ShareEvent
public import HashSig.SLHDSA.SHAKE128s.Proof.VerifyFree

/-!
# The real verifier's tally

The real game's verifier runs under `SharePresent.realWorldImpl`, which multiplies its tally by
`verifierCost` at every query: one verification call and the input, for a hash call; nothing, for
a coin. Read off the final tally of a run from `(1, cache)`:

* the record's size is the verification count (`count_eq`), and both are `0` when the request or
  the signature does not parse (`count_eq_zero_of_frame`, `count_eq_zero_of_parse`);
* on a parsed signature, at least `239` recorded inputs are free (`free_ge`): they locate no
  sensitive node and are prefixed by the public seed;
* every recorded input is either charged or free (`chargedOf_add_freeCost`), so the charged cost
  `ShareJoint.verifyCost` plus `239` is at most the count (`verifyCost_add_le`), and is `0` when
  nothing parses (`verifyCost_eq_zero`);
* an accepted verification counts at least `569` (`accepted_ge`).
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.VerifierTally

open Security RecordedQueries SharePresent ShareEvent

/-! ## Every input is charged or free -/

/-- **An input is charged by the shared charge or free, exactly one of the two.** -/
theorem chargedOf_add_freeCost (publicSeed : Digest) (input : Bytes) :
    ShareJoint.chargedOf publicSeed input + VerifyFree.freeCost publicSeed input = 1 := by
  classical
  unfold ShareJoint.chargedOf VerifyFree.freeCost VerifyFree.Free
  cases hloc : (GraphStakes.stakes publicSeed).locate input with
  | some node =>
    have hsp := ShareBound.seedPrefixed_of_locate publicSeed input (by rw [hloc]; rfl)
    simp [hsp]
  | none =>
    by_cases hsp : Target127.SeedPrefixed publicSeed input <;> simp [hsp]

/-- Over a multiset of inputs, the charged and the free weights add up to its size. -/
theorem sum_charged_add_sum_free (publicSeed : Digest) (inputs : Multiset Bytes) :
    (inputs.map (ShareJoint.chargedOf publicSeed)).sum +
        (inputs.map (VerifyFree.freeCost publicSeed)).sum = Multiset.card inputs := by
  rw [← Multiset.sum_map_add]
  simp [chargedOf_add_freeCost]

/-! ## One step of the tally -/

/-- One step multiplies the tally by the query's cost, which adds it additively. -/
theorem toAdd_step (tally : Multiplicative Tally) (queried : OracleWorld.Domain) :
    Multiplicative.toAdd (tally * Multiplicative.ofAdd (verifierCost queried)) =
      Multiplicative.toAdd tally + verifierCost queried := rfl

/-- The invariant: the record's size is the verification count. -/
@[expose] def Balanced (tally : Multiplicative Tally) : Prop :=
  Multiset.card (Multiplicative.toAdd tally).2 = (Multiplicative.toAdd tally).1 .verification

/-- The empty tally is balanced. -/
theorem balanced_one : Balanced 1 := rfl

/-- One step of the tally preserves balance. -/
theorem balanced_step (tally : Multiplicative Tally) (queried : OracleWorld.Domain)
    (h : Balanced tally) : Balanced (tally * Multiplicative.ofAdd (verifierCost queried)) := by
  unfold Balanced at h ⊢
  rw [toAdd_step, Prod.snd_add, Prod.fst_add, Multiset.card_add, Pi.add_apply, h]
  congr 1
  change Multiset.card (recordOf queried) =
    Counts.single .verification (hashCost queried) .verification
  rw [card_recordOf]
  simp [Counts.single]

/-- **Along a run of `realWorldImpl`, any invariant of the tally preserved by a step holds.** -/
theorem run_invariant {α : Type} (P : Multiplicative Tally → Prop)
    (hstep : ∀ tally queried, P tally → P (tally * Multiplicative.ofAdd (verifierCost queried)))
    (computation : OracleComp OracleWorld α) :
    ∀ (state : VerifyState), P state.1 →
      ∀ z ∈ support ((simulateQ realWorldImpl computation).run state), P z.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state hstate z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hstate
  | query_bind queried next ih =>
    intro state hstate z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep', hrest⟩ := hz
    rw [realWorldImpl_run] at hstep'
    obtain ⟨inner, -, rfl⟩ := ShareRealCap.exists_of_mem_support_map _ _ _ hstep'
    exact ih inner.1 _ (hstep _ _ hstate) z hrest

/-! ## The count -/

variable (pk : PublicKey) (request : Message) (wire : Bytes) (cache : QueryCache HashSpec)

/-- **The record's size is the verification count.** -/
theorem count_eq (w : Bool × VerifyState)
    (hw : w ∈ support ((simulateQ realWorldImpl
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run (1, cache))) :
    Multiset.card (Multiplicative.toAdd w.2.1).2 = (Multiplicative.toAdd w.2.1).1 .verification :=
  run_invariant Balanced balanced_step _ (1, cache) balanced_one w hw

/-- The verifier on an unparsed request or signature is `pure false`. -/
theorem state_of_verify_pure (w : Bool × VerifyState)
    (hpure : (Scheme.verify (m := OracleComp OracleWorld) pk request wire) = pure false)
    (hw : w ∈ support ((simulateQ realWorldImpl
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run (1, cache))) :
    w.2.1 = 1 := by
  rw [hpure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
  subst hw
  rfl

/-- The verifier on an unframed request is `pure false`. -/
theorem verify_eq_pure_of_frame (hframe : request.frame = none) :
    (Scheme.verify (m := OracleComp OracleWorld) pk request wire) = pure false := by
  simp only [Scheme.verify, hframe]

/-- The verifier on an unparsed signature is `pure false`. -/
theorem verify_eq_pure_of_parse (hparse : Signature.fromBytes? wire = none) :
    (Scheme.verify (m := OracleComp OracleWorld) pk request wire) = pure false := by
  cases hframe : request.frame with
  | none => simp only [Scheme.verify, hframe]
  | some message => simp only [Scheme.verify, hframe, hparse]

/-! ## The free queries -/

/-- The free queries of a tally's record. -/
@[expose] noncomputable def freeSum (publicSeed : Digest) (tally : Multiplicative Tally) : Nat :=
  ((Multiplicative.toAdd tally).2.map (VerifyFree.freeCost publicSeed)).sum

/-- A hash step adds the input's free cost to the free sum. -/
theorem freeSum_step (publicSeed : Digest) (tally : Multiplicative Tally) (input : Bytes) :
    freeSum publicSeed (tally * Multiplicative.ofAdd (verifierCost (Sum.inr input))) =
      freeSum publicSeed tally + VerifyFree.freeCost publicSeed input := by
  unfold freeSum
  rw [toAdd_step, Prod.snd_add, Multiset.map_add, Multiset.sum_add]
  simp [verifierCost, recordOf]

/-- **A flattened verifier run's free queries are those its instrumented run counts.** -/
theorem freeCounted_witness (publicSeed : Digest) {α : Type} (computation : OracleComp HashSpec α) :
    ∀ (state : VerifyState) (z : α × VerifyState),
      z ∈ support ((simulateQ realHashImpl computation).run state) →
      ∃ r ∈ support ((simulateQ realHashImpl
          (VerifyFree.freeCounted publicSeed computation)).run' state),
        freeSum publicSeed z.2.1 = freeSum publicSeed state.1 + Multiplicative.toAdd r.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨(value, Multiplicative.ofAdd 0), ?_, rfl⟩
    rw [VerifyFree.freeCounted_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure,
      support_pure]
    rfl
  | query_bind input next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    obtain ⟨htally, -, -⟩ := realHash_step input state.1 state.2 step hstep
    obtain ⟨r, hr, hsum⟩ := ih step.1 step.2 z hrest
    rw [StateT.run'_eq, support_map] at hr
    obtain ⟨⟨r', s'⟩, hrs, rfl⟩ := hr
    refine ⟨(r'.1, Multiplicative.ofAdd (VerifyFree.freeCost publicSeed input +
      Multiplicative.toAdd r'.2)), ?_, ?_⟩
    · rw [VerifyFree.freeCounted_query_bind, StateT.run'_eq, support_map]
      refine ⟨(_, s'), ?_, rfl⟩
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      refine ⟨step, hstep, ?_⟩
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      refine ⟨(r', s'), hrs, ?_⟩
      simp
    · rw [hsum, htally, freeSum_step]
      simp only [toAdd_ofAdd]
      omega

/-- **On a parsed signature, at least `239` recorded inputs are free.** -/
theorem free_ge (message : Bytes) (signature : Signature)
    (hframe : request.frame = some message) (hparse : Signature.fromBytes? wire = some signature)
    (w : Bool × VerifyState)
    (hw : w ∈ support ((simulateQ realWorldImpl
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run (1, cache))) :
    239 ≤ ((Multiplicative.toAdd w.2.1).2.map (VerifyFree.freeCost pk.seed)).sum := by
  rw [VerificationBudget.verify_lift, realWorldImpl_eq_add,
    QueryImpl.simulateQ_add_liftComp_right] at hw
  obtain ⟨r, hr, hsum⟩ := freeCounted_witness pk.seed _ (1, cache) w hw
  have h239 := (VerifyFree.verify_free pk request wire message signature hframe hparse).simulated
    realHashImpl (1, cache) r hr
  change 239 ≤ freeSum pk.seed w.2.1
  rw [hsum]
  exact h239.trans (Nat.le_add_left _ _)

/-! ## The form the joint cap consumes -/

/-- **On a parsed signature, the charged cost leaves `239` of the count.** -/
theorem verifyCost_add_le (message : Bytes) (signature : Signature)
    (hframe : request.frame = some message) (hparse : Signature.fromBytes? wire = some signature)
    (w : Bool × VerifyState)
    (hw : w ∈ support ((simulateQ realWorldImpl
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run (1, cache))) :
    ShareJoint.verifyCost pk.seed w.2 + 239 ≤ (Multiplicative.toAdd w.2.1).1 .verification := by
  have hfree := free_ge pk request wire cache message signature hframe hparse w hw
  have hsplit := sum_charged_add_sum_free pk.seed (Multiplicative.toAdd w.2.1).2
  rw [← count_eq pk request wire cache w hw, ← hsplit]
  unfold ShareJoint.verifyCost
  omega

/-- **On an unparsed request or signature, the charged cost is `0`.** -/
theorem verifyCost_eq_zero
    (hnone : request.frame = none ∨ Signature.fromBytes? wire = none)
    (w : Bool × VerifyState)
    (hw : w ∈ support ((simulateQ realWorldImpl
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run (1, cache))) :
    ShareJoint.verifyCost pk.seed w.2 = 0 := by
  have hpure : (Scheme.verify (m := OracleComp OracleWorld) pk request wire) = pure false := by
    rcases hnone with hframe | hparse
    · exact verify_eq_pure_of_frame pk request wire hframe
    · exact verify_eq_pure_of_parse pk request wire hparse
  unfold ShareJoint.verifyCost
  rw [state_of_verify_pure pk request wire cache w hpure hw]
  rfl

/-! ## An accepted verification -/

/-- **An accepted verification counts at least `569`.** -/
theorem accepted_ge (w : Bool × VerifyState)
    (hw : w ∈ support ((simulateQ realWorldImpl
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run (1, cache)))
    (haccept : w.1 = true) :
    569 ≤ (Multiplicative.toAdd w.2.1).1 .verification := by
  have hrec : ((w.1, Multiplicative.toAdd w.2.1), w.2.2) ∈ support
      ((simulateQ KeygenUniform.rom (countRecorded verifierCost
        (Scheme.verify (m := OracleComp OracleWorld) pk request wire))).run cache) := by
    rw [rom_verify_eq, support_map]
    exact ⟨w, hw, rfl⟩
  have hcount : (w.1, (Multiplicative.toAdd w.2.1).1) ∈ support
      ((simulateQ (RandomOracleModel.impl Bytes HashOutput)
        (countQueries VerificationBudget.verificationCost
          (Scheme.verify (m := OracleComp OracleWorld) pk request wire))).run' cache) := by
    rw [show countQueries VerificationBudget.verificationCost
        (Scheme.verify (m := OracleComp OracleWorld) pk request wire) =
        (fun result => (result.1, result.2.1)) <$> countRecorded verifierCost
          (Scheme.verify (m := OracleComp OracleWorld) pk request wire) from
      countQueries_verification_eq _, simulateQ_map, StateT.run'_eq, StateT.run_map,
      Functor.map_map, support_map]
    exact ⟨_, hrec, rfl⟩
  exact (VerificationBudget.verification_accepted_count_bounds pk request wire cache _ hcount
    haccept).1

end SlhDsaSecurity.VerifierTally
