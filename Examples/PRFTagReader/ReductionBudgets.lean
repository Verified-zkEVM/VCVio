/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.PRFTagReader.PRFReductions.Reductions
import VCVio.OracleComp.QueryTracking.Iter
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# PRF-query budgets for tag/reader reductions

Pathwise bounds for the actual multiple-session and single-session reductions.
Reader calls scan every slot, even after a match; exhausted tag calls can return
without a PRF query. The target predicate counts PRF calls and excludes private
uniform samples. These bounds do not assert a machine-runtime or PPT guarantee.
-/

public section

open OracleComp OracleSpec PRFTagReader

namespace PRFTagReader.QueryBudgets

variable {TagId Nonce Digest : Type} {sessionsPerTag : Nat}

/-- Combine existing per-interface budgets and transport their weighted sum through a handler.
The weights charge target PRF calls; private uniform samples are outside that target predicate. -/
private theorem fanout {I S A : Type} {target : OracleSpec I}
    (impl : QueryImpl (UnlinkOracleSpec TagId Nonce Digest) (StateT S (OracleComp target)))
    (p : I → Prop) [DecidablePred p] (readerCost tagCost : Nat)
    (hstep : ∀ q s, IsQueryBoundP ((impl q).run s) p
      (if q.isRight then readerCost else tagCost))
    (program : OracleComp (UnlinkOracleSpec TagId Nonce Digest) A)
    (qReader qTag : Nat)
    (hReader : IsQueryBoundP program (·.isRight) qReader)
    (hTag : IsQueryBoundP program (·.isLeft) qTag) (state : S) :
    IsQueryBoundP ((simulateQ impl program).run state) p
      (qReader * readerCost + qTag * tagCost) := by
  have joint := hReader.and_isQueryBound_pair hTag
  refine joint.simulateQ_run_of_step
    (impl := impl) (canQuery' := fun t b => ¬ p t ∨ 0 < b)
    (cost' := fun t b => if p t then b - 1 else b)
    (combine := (· + ·)) (mapBudget := fun b => b.1 * readerCost + b.2 * tagCost)
    (stepBudget := fun q _ => if q.isRight then readerCost else tagCost)
    ?_ ?_ ?_ state
  · exact fun h₁ h₂ => isQueryBoundP_bind h₁ (fun x _ => h₂ x)
  · intro q b s hcan
    exact hstep q s
  · intro q b hb
    rcases b with ⟨qr, qt⟩
    cases q with
    | inl tag =>
        simp only [Sum.isRight_inl, Bool.false_eq_true, not_false_eq_true,
          true_or, Sum.isLeft_inl, not_true_eq_false, false_or, true_and,
          ↓reduceIte] at hb ⊢
        nlinarith [Nat.sub_add_cancel (show 1 ≤ qt by omega)]
    | inr transcript =>
        simp only [Sum.isRight_inr, not_true_eq_false, false_or,
          Sum.isLeft_inr, Bool.false_eq_true, not_false_eq_true, true_or, and_true,
          ↓reduceIte] at hb ⊢
        nlinarith [Nat.sub_add_cancel (show 1 ≤ qr by omega)]

/-- An actual PRF call spends one unit of the PRF-only budget. -/
private theorem functionQuery_bound {D R : Type} (d : D) :
    IsQueryBoundP (PRFScheme.functionQuery (R := R) d) (·.isRight) 1 := by
  simp [PRFScheme.functionQuery]

/-- The reader scans every slot, including after an earlier matching digest. -/
private theorem reader_map_bound {Slot : Type} [Fintype Slot] (nonce : Nonce) :
    IsQueryBoundP
      ((Finset.univ : Finset Slot).toList.mapM
        (fun slot => PRFScheme.functionQuery (R := Digest) (slot, nonce)))
      (·.isRight) (Fintype.card Slot) := by
  simpa using isQueryBoundP_listMapM_const
    (fun slot => functionQuery_bound (R := Digest) (slot, nonce))
    (Finset.univ : Finset Slot).toList

/-- A multiple-session reader queries every tag once. -/
theorem multiple_reader_bound [Fintype TagId] [DecidableEq Digest]
    (transcript : TagTranscript Nonce Digest)
    (state : UnlinkState TagId) :
    IsQueryBoundP ((unlinkToMultiplePRFReaderImpl transcript).run state)
      (·.isRight) (Fintype.card TagId) := by
  simpa [unlinkToMultiplePRFReaderImpl, StateT.run_bind, StateT.run_monadLift,
    StateT.run_pure, bind_assoc, bind_pure_comp] using
    (reader_map_bound (Slot := TagId) (Digest := Digest) transcript.nonce)

/-- A single-session reader queries every tag and session slot once. -/
theorem single_reader_bound [Fintype TagId] [DecidableEq Digest]
    (transcript : TagTranscript Nonce Digest)
    (state : UnlinkState TagId) :
    IsQueryBoundP
      ((unlinkToSinglePRFReaderImpl (sessionsPerTag := sessionsPerTag) transcript).run state)
      (·.isRight) (Fintype.card TagId * sessionsPerTag) := by
  simpa [unlinkToSinglePRFReaderImpl, StateT.run_bind, StateT.run_monadLift,
    StateT.run_pure, bind_assoc, bind_pure_comp] using
    (reader_map_bound (Slot := TagId × Fin sessionsPerTag) (Digest := Digest) transcript.nonce)

/-- Lifting a private random computation issues no PRF queries. -/
private theorem private_randomness_bound {D R A : Type} (program : ProbComp A) :
    IsQueryBoundP (liftComp program (PRFScheme.PRFOracleSpec D R)) (·.isRight) 0 := by
  exact (isQueryBoundP_false program 0).liftComp_subSpec
    (fun _ => by change False ↔ false = true; simp)

variable [DecidableEq TagId] [SampleableType Nonce]

/-- A multiple-session tag issues at most one PRF call, including exhausted sessions. -/
theorem multiple_tag_bound (tag : TagId) (state : UnlinkState TagId) :
    IsQueryBoundP
      ((unlinkToMultiplePRFTagImpl (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) tag).run state) (·.isRight) 1 := by
  unfold unlinkToMultiplePRFTagImpl
  by_cases hs : state.sessionsUsed tag < sessionsPerTag
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, dite_eq_left hs,
      StateT.run_monadLift, monadLift_self, bind_assoc,
      StateT.run_pure, StateT.run_set, pure_bind]
    exact isQueryBoundP_bind (m := 1) (private_randomness_bound _) fun nonce _ => by
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      exact functionQuery_bound _
  · simp [hs]

/-- A single-session tag issues at most one PRF call, including exhausted sessions. -/
theorem single_tag_bound (tag : TagId) (state : UnlinkState TagId) :
    IsQueryBoundP
      ((unlinkToSinglePRFTagImpl (Nonce := Nonce) (Digest := Digest)
        (sessionsPerTag := sessionsPerTag) tag).run state) (·.isRight) 1 := by
  unfold unlinkToSinglePRFTagImpl
  by_cases hs : state.sessionsUsed tag < sessionsPerTag
  · simp only [StateT.run_bind, StateT.run_get, pure_bind, dite_eq_left hs,
      StateT.run_monadLift, monadLift_self, bind_assoc,
      StateT.run_pure, StateT.run_set, pure_bind]
    exact isQueryBoundP_bind (m := 1) (private_randomness_bound _) fun nonce _ => by
      simp only [bind_pure_comp, isQueryBoundP_map_iff]
      exact functionQuery_bound _
  · simp [hs]

variable [Fintype TagId] [DecidableEq Digest]

/-- The multiple-session handler charges one tag call or one call per reader slot. -/
theorem multiple_query_bound (q : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (state : UnlinkState TagId) :
    IsQueryBoundP
      ((unlinkToMultiplePRFQueryImpl (sessionsPerTag := sessionsPerTag) q).run state)
      (·.isRight) (if q.isRight then Fintype.card TagId else 1) := by
  cases q with
  | inl tag => simpa [unlinkToMultiplePRFQueryImpl] using multiple_tag_bound tag state
  | inr transcript =>
      simpa [unlinkToMultiplePRFQueryImpl] using multiple_reader_bound transcript state

/-- The single-session handler charges one tag call or one call per tag/session slot. -/
theorem single_query_bound (q : (UnlinkOracleSpec TagId Nonce Digest).Domain)
    (state : UnlinkState TagId) :
    IsQueryBoundP
      ((unlinkToSinglePRFQueryImpl (sessionsPerTag := sessionsPerTag) q).run state)
      (·.isRight) (if q.isRight then Fintype.card TagId * sessionsPerTag else 1) := by
  cases q with
  | inl tag => simpa [unlinkToSinglePRFQueryImpl] using single_tag_bound tag state
  | inr transcript =>
      simpa [unlinkToSinglePRFQueryImpl] using single_reader_bound transcript state

/-- The actual multiple-session distinguisher makes at most qTag + qReader * |TagId| PRF calls. -/
theorem multiple_reduction_bound (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    IsQueryBoundP (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag) adversary)
      (·.isRight) (qTag + qReader * Fintype.card TagId) := by
  unfold unlinkToMultiplePRFReduction
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  simpa only [Nat.mul_one, Nat.add_comm] using
    fanout (unlinkToMultiplePRFQueryImpl (sessionsPerTag := sessionsPerTag))
      (·.isRight) (Fintype.card TagId) 1 multiple_query_bound
      adversary qReader qTag hReader hTag UnlinkState.init

/-- The single-session reader scans every tag/session pair, so its multiplier includes s. -/
theorem single_reduction_bound (adversary : UnlinkAdversary TagId Nonce Digest)
    (qReader qTag : Nat)
    (hReader : IsQueryBoundP adversary (·.isRight) qReader)
    (hTag : IsQueryBoundP adversary (·.isLeft) qTag) :
    IsQueryBoundP (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag) adversary)
      (·.isRight) (qTag + qReader * Fintype.card TagId * sessionsPerTag) := by
  unfold unlinkToSinglePRFReduction
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  simpa only [Nat.mul_one, Nat.add_comm, Nat.mul_assoc] using
    fanout (unlinkToSinglePRFQueryImpl (sessionsPerTag := sessionsPerTag))
      (·.isRight) (Fintype.card TagId * sessionsPerTag) 1 single_query_bound
      adversary qReader qTag hReader hTag UnlinkState.init

end PRFTagReader.QueryBudgets
