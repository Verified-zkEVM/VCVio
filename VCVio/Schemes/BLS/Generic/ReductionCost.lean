/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.ReductionPrograms
import all VCVio.Schemes.BLS.Generic.Adversary
import all VCVio.Schemes.BLS.Generic.ReductionPrograms

/-! # Operation certificates for generic BLS reduction programs

The two extraction programs charge the adversary once per group operation. Private coins,
equality tests, encodings, cache lookups, and extraction arithmetic require no group operations.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace BLS.Generic

variable {F M R α : Type}

attribute [local implicit_reducible] spec handleSpec isGroupOp reductionLift

/-- Embedding a generic computation preserves its group-operation allowance. -/
theorem isQueryBoundP_reductionLift {A : OracleComp (genSpec F pairingSig) α} {q : ℕ}
    (h : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    IsQueryBoundP (simulateQ (reductionLift (M := M) (R := R)) A)
      (fun i => isGroupOp i = true) q := by
  apply ((isQueryBoundP_iff_weighted _ _).mp h).simulateQ_weighted
  rintro (t | n)
  · cases t <;> simp [reductionLift, isGroupOp, GroupModel.Query.isOp]
  · simp [reductionLift, isGroupOp]

private theorem coins_free {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp (genSpec F pairingSig) α)
      (fun i => isGroupOp i = true) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [liftM_pure, isQueryBoundP_pure]
  | query_bind t k ih =>
      simp only [liftM_bind]
      refine isQueryBoundP_bind ?_ fun x _ => ih x
      change IsQueryBoundP (liftM ((genSpec F pairingSig).query (.inr t))) _ 0
      simp [isGroupOp]

/-- Closing the private scalar oracle preserves the group-operation allowance. -/
theorem isQueryBoundP_closeReduction [DecidableEq M] [SampleableType R]
    {A : OracleComp (reductionSpec F M R) α} {q : ℕ}
    (h : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    IsQueryBoundP (closeReduction A) (fun i => isGroupOp i = true) q := by
  unfold closeReduction StateT.run'
  rw [isQueryBoundP_map_iff]
  apply h.simulateQ_run_StateT_of_step
  rintro (t | n | m) cache
  · cases t <;> simp [reductionCache, StateT.run, isGroupOp, GroupModel.Query.isOp]
  · simp [reductionCache, StateT.run, isGroupOp]
  · exact coins_free _

/-- Per-query charges for adversarial group work, direct hashing, and signing. -/
@[expose] def reductionCharge (cH cS : ℕ) (t : (adversarySpec F M).Domain) : ℕ :=
  (if isGroupOp t then 1 else 0) + (if isHash t then cH else 0) +
    (if isSign t then cS else 0)

/-- The virtual reduction handler charges exactly the supplied hash and signing allowances. -/
theorem costCertificate_reductionHandler [CommSemiring F] [DecidableEq F]
    (z : PSort → Handle) (hash sign : R → OracleComp (genSpec F pairingSig) Handle)
    (cH cS : ℕ)
    (hH : ∀ r, IsQueryBoundP (hash r) (fun i => isGroupOp i = true) cH)
    (hS : ∀ r, IsQueryBoundP (sign r) (fun i => isGroupOp i = true) cS) :
    CostCertificate (reductionHandler (M := M) z hash sign) (reductionCharge cH cS) := by
  rintro (t | t | n | t) st
  · simp only [reductionHandler, StateT.run, bind_pure_comp, isQueryBoundP_map_iff]
    have hc := isQueryBoundP_reductionLift (M := M) (R := R)
      (costCertificate_virtualizeImpl (F := F) z (.inl t) st.handles)
    convert hc using 1 <;> rfl
  · simp [reductionHandler, StateT.run, reductionCharge, isHash, isSign, isGroupOp]
  · simp [reductionHandler, StateT.run, reductionCharge, isHash, isSign, isGroupOp]
  · rcases t with ⟨m | m, groups⟩
    all_goals
      simp only [reductionHandler, StateT.run, Bool.false_eq_true, ↓reduceIte,
        bind_pure_comp, isQueryBoundP_query_bind_iff, isGroupOp, Bool.false_eq_true,
        ↓reduceIte, isQueryBoundP_map_iff]
    · simpa [reductionCharge, isHash, isSign, isGroupOp] using
        (fun r => isQueryBoundP_reductionLift (M := M) (R := R) (hH r))
    · simpa [reductionCharge, isHash, isSign, isGroupOp] using
        (fun r => isQueryBoundP_reductionLift (M := M) (R := R) (hS r))

private def budgetPredicate (k : Fin 3) : (adversarySpec F M).Domain → Prop :=
  ![fun i => isGroupOp i = true, isHash, isSign] k

private instance budgetPredicateDecidable (k : Fin 3) :
    DecidablePred (budgetPredicate (F := F) (M := M) k) := by
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => Fin.elim0 i) k) k) k
  all_goals dsimp [budgetPredicate]; infer_instance

/-- Running the certified virtual handler combines the three independent adversary budgets. -/
theorem isQueryBoundP_reductionHandler_run [CommSemiring F] [DecidableEq F]
    (z : PSort → Handle) (hash sign : R → OracleComp (genSpec F pairingSig) Handle)
    (cH cS : ℕ)
    (hH : ∀ r, IsQueryBoundP (hash r) (fun i => isGroupOp i = true) cH)
    (hS : ∀ r, IsQueryBoundP (sign r) (fun i => isGroupOp i = true) cS)
    (program : OracleComp (adversarySpec F M) α) (q qH qS : ℕ)
    (hq : IsQueryBoundP program (fun i => isGroupOp i = true) q)
    (hqH : IsQueryBoundP program isHash qH) (hqS : IsQueryBoundP program isSign qS)
    (st : ReductionState F M) :
    IsQueryBoundP ((simulateQ (reductionHandler z hash sign) program).run st)
      (fun i => isGroupOp i = true) (q + cH * qH + cS * qS) := by
  have hb : ∀ k : Fin 3, IsQueryBoundP program (budgetPredicate k) (![q, qH, qS] k) := by
    intro k
    fin_cases k
    · convert hq using 1 <;> rfl
    · convert hqH using 1 <;> rfl
    · convert hqS using 1 <;> rfl
  have hw := isQueryBound_weighted_of_predicates budgetPredicate ![1, cH, cS] ![q, qH, qS] hb
  have hc : CostCertificate (reductionHandler (M := M) z hash sign)
      (fun t => ∑ k : Fin 3, if budgetPredicate k t then ![1, cH, cS] k else 0) := by
    convert costCertificate_reductionHandler (M := M) z hash sign cH cS hH hS using 1
    funext t
    simp [budgetPredicate, Fin.sum_univ_succ, reductionCharge, Nat.add_assoc]
  simpa [Fin.sum_univ_succ, Nat.add_assoc] using hc.simulateQ_run hw st

private theorem readTranscript_free (hash sign : R → F × F)
    (tr : LinearFunctional.Transcript M) :
    IsQueryBoundP (simulateQ (fun q => ((reductionSpec F M R).query (.inr q) :
      OracleComp (reductionSpec F M R) _)) (LinearFunctional.readTranscript hash sign tr))
      (fun i => isGroupOp i = true) 0 := by
  induction tr with
  | nil => simp [LinearFunctional.readTranscript]
  | cons t tr ih =>
    rcases t with ⟨kind, m⟩
    simpa [LinearFunctional.readTranscript, isGroupOp] using (fun (_ : R) => ih)

/-- Chronological replay and scalar extraction add no group operations to the handler run. -/
theorem isQueryBoundP_reductionExtract [CommSemiring F] [DecidableEq F]
    (A : Adversary F M) (z : PSort → Handle) (pk₁ pk₂ : Handle)
    (hash sign : R → OracleComp (genSpec F pairingSig) Handle)
    (hashRep signRep : R → F × F) (initial : List (F × F))
    (cH cS q qH qS : ℕ)
    (hH : ∀ r, IsQueryBoundP (hash r) (fun i => isGroupOp i = true) cH)
    (hS : ∀ r, IsQueryBoundP (sign r) (fun i => isGroupOp i = true) cS)
    (hq : IsQueryBoundP (A reductionInput) (fun i => isGroupOp i = true) q)
    (hqH : IsQueryBoundP (A reductionInput) isHash qH)
    (hqS : IsQueryBoundP (A reductionInput) isSign qS) :
    IsQueryBoundP (reductionExtract A z pk₁ pk₂ hash sign hashRep signRep initial)
      (fun i => isGroupOp i = true) (q + cH * qH + cS * qS) := by
  unfold reductionExtract
  apply (isQueryBoundP_bind
    (isQueryBoundP_reductionHandler_run z hash sign cH cS hH hS _ q qH qS hq hqH hqS
      (initialReductionState pk₁ pk₂)) (m := 0) ?_).mono (by omega)
  rintro ⟨out, st⟩ _
  dsimp only
  apply isQueryBoundP_bind (m := 0) (readTranscript_free hashRep signRep st.transcript)
  intro basis _
  simp [isGroupOp]

/-- The invalid-handle setup uses exactly three scalar multiplications. -/
theorem isQueryBoundP_reductionZeros [Zero F] :
    IsQueryBoundP (reductionZeros (F := F)) (fun i => isGroupOp i = true) 3 := by
  simp [reductionZeros, isGroupOp, GroupModel.Query.isOp]

/-- A masked challenge point costs at most three group operations. -/
theorem isQueryBoundP_maskedPoint (r : F × F) :
    IsQueryBoundP (maskedPoint r) (fun i => isGroupOp i = true) 3 := by
  simp [maskedPoint, isGroupOp, GroupModel.Query.isOp]

/-- The good extraction program costs three setup operations and one per hash or signature. -/
theorem isQueryBoundP_goodProgram [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M]
    (A : Adversary F M) (q qH qS : ℕ)
    (hq : IsQueryBoundP (A reductionInput) (fun i => isGroupOp i = true) q)
    (hqH : IsQueryBoundP (A reductionInput) isHash qH)
    (hqS : IsQueryBoundP (A reductionInput) isSign qS) :
    IsQueryBoundP (goodProgram A) (fun i => isGroupOp i = true) (3 + q + qH + qS) := by
  unfold goodProgram
  apply isQueryBoundP_closeReduction
  apply (isQueryBoundP_bind (isQueryBoundP_reductionLift isQueryBoundP_reductionZeros)
    (m := q + 1 * qH + 1 * qS) ?_).mono (by omega)
  intro z _
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  apply isQueryBoundP_reductionExtract _ _ _ _ _ _ _ _ _ 1 1 q qH qS
    (fun _ => by simp [isGroupOp, GroupModel.Query.isOp])
    (fun _ => by simp [isGroupOp, GroupModel.Query.isOp]) hq hqH hqS

/-- The bad extraction program costs five setup operations, three per hash, and four per sign. -/
theorem isQueryBoundP_badProgram [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M]
    (A : Adversary F M) (q qH qS : ℕ)
    (hq : IsQueryBoundP (A reductionInput) (fun i => isGroupOp i = true) q)
    (hqH : IsQueryBoundP (A reductionInput) isHash qH)
    (hqS : IsQueryBoundP (A reductionInput) isSign qS) :
    IsQueryBoundP (badProgram A) (fun i => isGroupOp i = true) (5 + q + 3 * qH + 4 * qS) := by
  unfold badProgram
  apply isQueryBoundP_closeReduction
  have hcoins : IsQueryBoundP (liftM ($ᵗ F) : OracleComp (reductionSpec F M (F × F)) F)
      (fun i => isGroupOp i = true) 0 := by
    generalize ($ᵗ F) = oa
    induction oa using OracleComp.inductionOn with
    | pure x => simp only [liftM_pure, isQueryBoundP_pure]
    | query_bind t k ih =>
      simp only [liftM_bind]
      refine isQueryBoundP_bind ?_ fun x _ => ih x
      change IsQueryBoundP
        (liftM ((reductionSpec F M (F × F)).query (.inr (.inl t)))) _ 0
      simp [isGroupOp]
  apply (isQueryBoundP_bind hcoins (m := 5 + q + 3 * qH + 4 * qS) ?_).mono (by omega)
  intro κ _
  apply (isQueryBoundP_bind (isQueryBoundP_reductionLift isQueryBoundP_reductionZeros)
    (m := 2 + q + 3 * qH + 4 * qS) ?_).mono (by omega)
  intro z _
  simp only [isQueryBoundP_query_bind_iff, isGroupOp, GroupModel.Query.isOp_smul,
    Sum.elim_inl, ↓reduceIte, not_true_eq_false, false_or]
  refine ⟨by omega, fun pk₁ => ⟨by omega, fun pk₂ => ?_⟩⟩
  rw [bind_pure_comp, isQueryBoundP_map_iff]
  have hs (r : F × F) : IsQueryBoundP (do
      let h ← maskedPoint r
      (genSpec F pairingSig).query (.inl (.smul .g₁ κ h)))
      (fun i => isGroupOp i = true) 4 :=
    by
      apply isQueryBoundP_bind (m := 1) (isQueryBoundP_maskedPoint r)
      intro h _
      simp [isGroupOp, GroupModel.Query.isOp]
  exact (isQueryBoundP_reductionExtract A z pk₁ pk₂ _ _ _ _ _ 3 4 q qH qS
    isQueryBoundP_maskedPoint hs hq hqH hqS).mono (by omega)

end BLS.Generic
