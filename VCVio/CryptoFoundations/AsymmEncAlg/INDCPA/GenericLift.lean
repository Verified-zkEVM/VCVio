/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.Oracle
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime
public import ToMathlib.Control.StateT
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-!
# Asymmetric Encryption Schemes: Generic IND-CPA Lifts

This file contains the generic step-adversary extraction and the one-time-to-many-time IND-CPA
lift.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

universe u v w

namespace AsymmEncAlg

variable {M PK SK C : Type}

section MultiQueryToOneTime

variable [DecidableEq M]
variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

/-- Result of running the generic step-adversary prefix simulation. Either the oracle adversary
has already terminated, or we have paused exactly at the target fresh LR query and captured the
messages plus the continuation waiting for the challenge ciphertext. -/
inductive IND_CPA_StepResult (α : Type)
  | done (a : α) : IND_CPA_StepResult α
  | paused (mm : M × M) (cont : C → OracleComp encAlg'.IND_CPA_oracleSpec α) :
      IND_CPA_StepResult α

/-- Prefix simulation for the generic step adversary. Starting from counter value `n ≤ k`, it
answers the first `k - n` fresh LR queries with the left branch, stops at the next fresh LR
query, and records the continuation. -/
def IND_CPA_stepPrefix (pk : PK) (k : ℕ) {α : Type} :
    OracleComp encAlg'.IND_CPA_oracleSpec α →
      StateT encAlg'.IND_CPA_CountedState ProbComp (IND_CPA_StepResult (encAlg' := encAlg') α) :=
  OracleComp.construct
    (C := fun (_ : OracleComp encAlg'.IND_CPA_oracleSpec α) =>
      StateT encAlg'.IND_CPA_CountedState ProbComp
        (IND_CPA_StepResult (encAlg' := encAlg') α))
    (fun a => pure (.done a))
    (fun t oa rec =>
      match t with
      | .inl tu => do rec (←$[0..tu])
      | .inr mm =>
          do
            let st ← get
            match st.1 mm with
            | some c => rec c
            | none =>
                if st.2 < k then
                  let c ← encAlg'.encrypt pk mm.1
                  let cache' := st.1.cacheQuery mm c
                  set (cache', st.2 + 1)
                  rec c
                else
                  pure (.paused mm oa))

/-- State carried by the generic extracted one-time adversary for the `k`-th adjacent hybrid
gap. If the original oracle adversary already terminated before issuing the target fresh query,
we store its final guess. Otherwise we store the paused continuation and counted cache state. -/
inductive IND_CPA_StepState
  | done (guess : Bool) : IND_CPA_StepState
  | paused (pk : PK) (mm : M × M) (st : encAlg'.IND_CPA_CountedState)
      (cont : C → OracleComp encAlg'.IND_CPA_oracleSpec Bool) : IND_CPA_StepState

/-- Generic extraction of the one-time adversary for the `k`-th fresh LR query. -/
def IND_CPA_stepAdversary [Inhabited M] (adversary : encAlg'.IND_CPA_Adversary) (k : ℕ) :
    IND_CPA_OneTime_Adversary encAlg' where
  State := IND_CPA_StepState (encAlg' := encAlg')
  chooseMessages pk := do
    let ⟨res, st⟩ ← (IND_CPA_stepPrefix (encAlg' := encAlg') pk k (adversary pk)).run (∅, 0)
    match res with
    | .done guess => pure (default, default, .done guess)
    | .paused mm cont => pure (mm.1, mm.2, .paused pk mm st cont)
  distinguish state c := do
    match state with
    | .done guess => pure guess
    | .paused pk mm st cont =>
        let st' := (st.1.cacheQuery mm c, st.2 + 1)
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run' st'

/-- Unfold `IND_CPA_stepPrefix` on a pure computation. -/
private lemma IND_CPA_stepPrefix_pure (pk : PK) (k : ℕ) {α : Type} (a : α) :
    IND_CPA_stepPrefix (encAlg' := encAlg') pk k (pure a) = pure (.done a) := rfl

/-- Unfold `IND_CPA_stepPrefix` through a query to the uniform side of the oracle spec. -/
private lemma IND_CPA_stepPrefix_query_inl (pk : PK) (k : ℕ) {α : Type} (tu : unifSpec.Domain)
    (mx : encAlg'.IND_CPA_oracleSpec.Range (Sum.inl tu) →
      OracleComp encAlg'.IND_CPA_oracleSpec α) :
    IND_CPA_stepPrefix (encAlg' := encAlg') pk k
        (encAlg'.IND_CPA_oracleSpec.query (Sum.inl tu) >>= mx) =
      (do
        let u ← $[0..tu]
        IND_CPA_stepPrefix (encAlg' := encAlg') pk k (mx u)) := rfl

/-- Unfold `IND_CPA_stepPrefix` through an LR challenge query. -/
private lemma IND_CPA_stepPrefix_query_inr (pk : PK) (k : ℕ) {α : Type} (mm : M × M)
    (mx : encAlg'.IND_CPA_oracleSpec.Range (Sum.inr mm) →
      OracleComp encAlg'.IND_CPA_oracleSpec α) :
    IND_CPA_stepPrefix (encAlg' := encAlg') pk k
        (encAlg'.IND_CPA_oracleSpec.query (Sum.inr mm) >>= mx) =
      (do
        let st ← get
        match st.1 mm with
        | some c =>
            IND_CPA_stepPrefix (encAlg' := encAlg') pk k (mx c)
        | none =>
            if st.2 < k then do
              let c ← (encAlg'.encrypt pk mm.1)
              let cache' := st.1.cacheQuery mm c
              set (cache', st.2 + 1)
              IND_CPA_stepPrefix (encAlg' := encAlg') pk k (mx c)
            else
              pure (.paused mm mx)) := rfl

/-- Once the counter has already crossed `k`, the `k` and `k + 1` counted hybrids agree. -/
private lemma IND_CPA_hybridLR_counted_run'_evalSPMF_eq_above (pk : PK) (k : ℕ) {α : Type}
    (oa : OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hst : k + 1 ≤ st.2) :
    𝒮[(simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) oa).run' st] =
      𝒮[(simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (k + 1)) oa).run' st] := by
  simp only [StateT.run', evalSPMF_map]
  exact congrArg (Prod.fst <$> ·) <| evalSPMF_ext fun z =>
    OracleComp.ProgramLogic.Relational.probOutput_simulateQ_run_eq_of_impl_eq_preservesInv
      (impl₁ := encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k)
      (impl₂ := encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (k + 1))
      (Inv := fun s => k + 1 ≤ s.2) (oa := oa)
      (himpl_eq := IND_CPA_hybridLR_counted_run_eq_of_le (encAlg' := encAlg') pk k)
      (hpres₂ := fun t s hs z hz => by
        have := IND_CPA_hybridLR_counted_counter_le (encAlg' := encAlg') pk (k + 1) t s z hz
        omega)
      (s := st) (hs := hst) (z := z)

/-- Once the counter has already crossed `k`, the `k` and `if branch then k + 1 else k` counted
hybrids agree: when `branch` selects the higher index this is the adjacent-hybrid step, otherwise
both indices coincide. -/
private lemma IND_CPA_hybridLR_counted_run'_evalSPMF_eq_branch (pk : PK) (k : ℕ) (branch : Bool)
    {α : Type} (oa : OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hst : k + 1 ≤ st.2) :
    𝒮[(simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) oa).run' st] =
      𝒮[(simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (if branch then k + 1 else k))
          oa).run' st] := by
  cases branch
  · rfl
  · exact IND_CPA_hybridLR_counted_run'_evalSPMF_eq_above (encAlg' := encAlg') pk k oa st hst

/-- Unfold one counted LR hybrid step on a uniform query, exposing the uniform sample followed by
the continuation run on the unchanged counted state. -/
private lemma IND_CPA_queryImpl_hybridLR_counted_run'_inl (pk : PK) (leftUntil : ℕ) {α : Type}
    (tu : unifSpec.Domain)
    (oa : encAlg'.IND_CPA_oracleSpec.Range (.inl tu) → OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) :
    (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
        (encAlg'.IND_CPA_oracleSpec.query (.inl tu) >>= oa)).run' st =
      (do
        let u ← ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu))
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)).run' st) := by
  have hrun :
      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
          (encAlg'.IND_CPA_oracleSpec.query (.inl tu) >>= oa)).run st =
        (($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu)) >>= fun u =>
          (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u)).run st) := by
    rw [simulateQ_query_bind, StateT.run_bind]
    change
      (($ᵗ (unifSpec.Range tu) :
          StateT encAlg'.IND_CPA_CountedState ProbComp (unifSpec.Range tu)).run st >>= fun p =>
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa p.1)).run p.2) = _
    rw [StateT.run_liftM]
    simp
  rw [StateT.run'_eq, hrun]
  simp [StateT.run'_eq]

/-- Unfold one counted LR hybrid step on a fresh (cache-miss) LR query, exposing the encryption
of the selected branch followed by the continuation run on the incremented cache. -/
private lemma IND_CPA_queryImpl_hybridLR_counted_run'_inr_none (pk : PK) (leftUntil : ℕ) {α : Type}
    (mm : M × M) (oa : C → OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hcache : st.1 mm = none) :
    (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
        (encAlg'.IND_CPA_oracleSpec.query (.inr mm) >>= oa)).run' st =
      (do
        let c ← encAlg'.encrypt pk (if st.2 < leftUntil then mm.1 else mm.2)
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
          (oa c)).run' (st.1.cacheQuery mm c, st.2 + 1)) := by
  change encAlg'.IND_CPA_oracleSpec.Range (.inr mm) →
    OracleComp encAlg'.IND_CPA_oracleSpec α at oa
  have hrun :
      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
          (encAlg'.IND_CPA_oracleSpec.query (.inr mm) >>= oa)).run st =
        (do
          let c ← encAlg'.encrypt pk (if st.2 < leftUntil then mm.1 else mm.2)
          (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
            (oa c)).run (st.1.cacheQuery mm c, st.2 + 1)) := by
    rw [simulateQ_query_bind, StateT.run_bind]
    change
      ((encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk leftUntil mm).run st >>= fun u =>
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u.1)).run u.2) = _
    rw [IND_CPA_hybridChallengeOracleLR_counted_run_none (encAlg' := encAlg') pk leftUntil mm st
      hcache]
    simp
  rw [StateT.run'_eq, hrun]
  simp [StateT.run'_eq]

/-- Unfold one counted LR hybrid step on a cached (cache-hit) LR query: the cache is reused and the
continuation runs unchanged on the same state. -/
private lemma IND_CPA_queryImpl_hybridLR_counted_run'_inr_some (pk : PK) (leftUntil : ℕ) {α : Type}
    (mm : M × M) (c : C) (oa : C → OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hcache : st.1 mm = some c) :
    (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
        (encAlg'.IND_CPA_oracleSpec.query (.inr mm) >>= oa)).run' st =
      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa c)).run' st := by
  change encAlg'.IND_CPA_oracleSpec.Range (.inr mm) →
    OracleComp encAlg'.IND_CPA_oracleSpec α at oa
  have hrun :
      (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil)
          (encAlg'.IND_CPA_oracleSpec.query (.inr mm) >>= oa)).run st =
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa c)).run st := by
    rw [simulateQ_query_bind, StateT.run_bind]
    change
      ((encAlg'.IND_CPA_hybridChallengeOracleLR_counted pk leftUntil mm).run st >>= fun u =>
        (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk leftUntil) (oa u.1)).run u.2) = _
    rw [IND_CPA_hybridChallengeOracleLR_counted_run_some (encAlg' := encAlg') pk leftUntil mm c st
      hcache]
    rfl
  rw [StateT.run'_eq, hrun]
  simp [StateT.run'_eq]

/-- Planned semantic bridge: resuming the paused prefix simulation with the chosen branch should
match the corresponding counted LR hybrid on the same sample space. This is the core local
decomposition lemma needed for the generic step-adversary proof. -/
private lemma IND_CPA_stepPrefix_resume_eq_hybridLR (pk : PK) (k : ℕ) (branch : Bool) {α : Type}
    (oa : OracleComp encAlg'.IND_CPA_oracleSpec α)
    (st : encAlg'.IND_CPA_CountedState) (hst : st.2 ≤ k) :
    𝒮[(do
        let ⟨res, st'⟩ ← (IND_CPA_stepPrefix (encAlg' := encAlg') pk k oa).run st
        match res with
        | .done a => pure a
        | .paused mm cont =>
            let c ← encAlg'.encrypt pk (if branch then mm.1 else mm.2)
            let st'' := (st'.1.cacheQuery mm c, st'.2 + 1)
            (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk k) (cont c)).run' st'')] =
      𝒮[(simulateQ
            (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk (if branch then k + 1 else k))
            oa).run' st] := by
  revert st hst
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro st hst
      simp [IND_CPA_stepPrefix_pure]
  | query_bind t oa ih =>
      intro st hst
      cases t with
      | inl tu =>
          refine evalSPMF_ext fun x => ?_
          rw [IND_CPA_stepPrefix_query_inl, IND_CPA_queryImpl_hybridLR_counted_run'_inl
            (encAlg' := encAlg') pk (if branch then k + 1 else k) tu oa st]
          simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
          exact probOutput_bind_congr' ($ᵗ (unifSpec.Range tu) : ProbComp (unifSpec.Range tu)) x
            fun u => (evalSPMF_ext_iff.mp (ih u st hst)) x
      | inr mm =>
          rcases hcache : st.1 mm with _ | c
          · by_cases hlt : st.2 < k
            · refine evalSPMF_ext fun x => ?_
              rw [IND_CPA_stepPrefix_query_inr]
              simp only [hcache, hlt, StateT.run_bind, StateT.run_get, StateT.run_set,
                ↓reduceIte, pure_bind, bind_assoc, StateT.run_liftM]
              rw [IND_CPA_queryImpl_hybridLR_counted_run'_inr_none (encAlg' := encAlg') pk
                  (if branch then k + 1 else k) mm oa st hcache,
                ite_eq_left (show st.2 < if branch then k + 1 else k by cases branch <;> simp_all)]
              exact probOutput_bind_congr' (encAlg'.encrypt pk mm.1) x
                fun c => (evalSPMF_ext_iff.mp (ih c (st.1.cacheQuery mm c, st.2 + 1) (by omega))) x
            · have hEq : st.2 = k := by omega
              refine evalSPMF_ext fun x => ?_
              rw [IND_CPA_stepPrefix_query_inr]
              simp only [hcache, hlt, StateT.run_bind, StateT.run_get, StateT.run_pure,
                ite_false, pure_bind]
              rw [IND_CPA_queryImpl_hybridLR_counted_run'_inr_none (encAlg' := encAlg') pk
                  (if branch then k + 1 else k) mm oa st hcache,
                show (if st.2 < if branch then k + 1 else k then mm.1 else mm.2) =
                  (if branch then mm.1 else mm.2) by cases branch <;> simp [hEq]]
              exact probOutput_bind_congr' (encAlg'.encrypt pk (if branch then mm.1 else mm.2)) x
                fun c => (evalSPMF_ext_iff.mp (IND_CPA_hybridLR_counted_run'_evalSPMF_eq_branch
                  (encAlg' := encAlg') pk k branch (oa c)
                  (st.1.cacheQuery mm c, st.2 + 1) (by omega))) x
          · refine evalSPMF_ext fun x => ?_
            rw [IND_CPA_stepPrefix_query_inr]
            simp only [hcache, StateT.run_bind, StateT.run_get, pure_bind]
            rw [IND_CPA_queryImpl_hybridLR_counted_run'_inr_some (encAlg' := encAlg') pk
              (if branch then k + 1 else k) mm c oa st hcache]
            exact (evalSPMF_ext_iff.mp (ih c st hst)) x

/-- The one-time IND-CPA game of the extracted step adversary is the uniform-bit branch between
adjacent LR hybrids. -/
private lemma IND_CPA_stepAdversary_game_eq_hybridBranch [Inhabited M]
    (adversary : encAlg'.IND_CPA_Adversary) (k : ℕ) :
    IND_CPA_OneTime_Game (encAlg := encAlg')
        (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k) ProbCompRuntime.probComp =
      𝒟[do
          let bit ← ($ᵗ Bool)
          let z ← if bit then encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)
                   else encAlg'.IND_CPA_LR_hybridGame adversary k
          pure (bit == z)] := by
  show 𝒟[($ᵗ Bool) >>= fun bit => _] = _
  refine evalDist_eq_of_evalSPMF_eq _ _ (evalSPMF_ext fun x => ?_)
  refine probOutput_bind_congr' ($ᵗ Bool) x fun bit => ?_
  change Pr[= x | do
      let (pk, _sk) ← encAlg'.keygen
      let (m₁, m₂, state) ←
        (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k).chooseMessages pk
      let c ← encAlg'.encrypt pk (if bit then m₁ else m₂)
      let b' ← (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k).distinguish state c
      pure (bit == b')] =
    Pr[= x | do
      let z ← if bit then encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)
               else encAlg'.IND_CPA_LR_hybridGame adversary k
      pure (bit == z)]
  simp only [IND_CPA_LR_hybridGame, monad_norm,
    ← apply_ite (f := fun g => encAlg'.keygen >>= g)]
  refine probOutput_bind_congr' encAlg'.keygen x fun pk_sk => ?_
  simp only [IND_CPA_stepAdversary, monad_norm,
    apply_ite (f := fun h : PK × SK → ProbComp Bool => h pk_sk),
    ← apply_ite (f := fun n => (do
      let b' ← (simulateQ (encAlg'.IND_CPA_queryImpl_hybridLR_counted pk_sk.1 n)
        (adversary pk_sk.1)).run' (∅, 0)
      pure (bit == b') : ProbComp Bool))]
  rw [probOutput_def, probOutput_def]
  congr 1
  have hresume := IND_CPA_stepPrefix_resume_eq_hybridLR (encAlg' := encAlg')
    pk_sk.1 k bit (adversary pk_sk.1) (∅, 0) (Nat.zero_le k)
  dsimp at hresume
  have hmap (mx : ProbComp Bool) :
      (do let b' ← mx; pure (bit == b')) = (bit == ·) <$> mx := by
    rw [map_eq_bind_pure_comp]
    rfl
  refine evalSPMF_ext fun y => ?_
  conv_rhs =>
    rw [StateT.run'_eq, hmap]
  refine Eq.trans ?_ (probOutput_map_eq_of_evalSPMF_eq hresume (bit == ·) y)
  simp only [monad_norm]
  refine probOutput_bind_congr'
    ((IND_CPA_stepPrefix (encAlg' := encAlg') pk_sk.1 k (adversary pk_sk.1)).run (∅, 0)) y
    fun ⟨res, _st⟩ => ?_
  cases res <;> simp

end MultiQueryToOneTime

section MultiQueryHybridLift

variable [DecidableEq M]
variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

/-- The one-time IND-CPA advantage of the extracted step adversary is the distinguishing advantage
between adjacent LR hybrids. -/
theorem IND_CPA_OneTime_Advantage_stepAdversary [Inhabited M]
    (adversary : encAlg'.IND_CPA_Adversary) (k : ℕ) :
    IND_CPA_OneTime_Advantage encAlg' ProbCompRuntime.probComp
        (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k) =
      𝒟[encAlg'.IND_CPA_LR_hybridGame adversary (k + 1)].boolDist
        𝒟[encAlg'.IND_CPA_LR_hybridGame adversary k] := by
  rw [IND_CPA_OneTime_Advantage, IND_CPA_stepAdversary_game_eq_hybridBranch,
    evalDist_boolBias_bind_uniformBool]

/-- Generic one-time-to-many-time lift: the IND-CPA advantage of an oracle adversary making at
most `q` fresh LR queries is at most the sum of the one-time advantages of the extracted step
adversaries. -/
theorem IND_CPA_Advantage_le_sum_oneTime_stepAdversary
    [Inhabited M] [Finite C] [Inhabited C]
    (adversary : encAlg'.IND_CPA_Adversary) (q : ℕ)
    (hq : adversary.MakesAtMostQueries q) :
    IND_CPA_Advantage (encAlg := encAlg') adversary ≤
      ∑ k ∈ Finset.range q, IND_CPA_OneTime_Advantage encAlg' ProbCompRuntime.probComp
        (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k) := by
  have hleft := evalDist_eq_of_evalSPMF_eq _ _
    (encAlg'.IND_CPA_LR_hybridGame_q_evalSPMF_eq_left_of_MakesAtMostQueries adversary q hq)
  have hright := evalDist_eq_of_evalSPMF_eq _ _
    (encAlg'.IND_CPA_LR_hybridGame_zero_evalSPMF_eq_right adversary)
  rw [IND_CPA_Advantage_eq_boolDist_LR, ← hleft, ← hright, MeasureTheory.Measure.boolDist_comm]
  refine (MeasureTheory.Measure.boolDist_le_sum_range
    (fun i ↦ 𝒟[encAlg'.IND_CPA_LR_hybridGame adversary i]) q).trans_eq
    (Finset.sum_congr rfl fun k _ ↦ ?_)
  rw [IND_CPA_OneTime_Advantage_stepAdversary, MeasureTheory.Measure.boolDist_comm]

/-- Uniform corollary of the generic lift: if every one-time adversary has advantage at most `ε`,
then any `q`-query oracle adversary has IND-CPA advantage at most `q * ε`. -/
theorem IND_CPA_Advantage_le_mul_of_oneTime_bound
    [Inhabited M] [Finite C] [Inhabited C]
    (adversary : encAlg'.IND_CPA_Adversary) (q : ℕ) (ε : ℝ≥0∞)
    (hq : adversary.MakesAtMostQueries q)
    (hstep : ∀ adv : IND_CPA_OneTime_Adversary encAlg',
      IND_CPA_OneTime_Advantage encAlg' ProbCompRuntime.probComp adv ≤ ε) :
    IND_CPA_Advantage (encAlg := encAlg') adversary ≤ q * ε :=
  (IND_CPA_Advantage_le_sum_oneTime_stepAdversary adversary q hq).trans <|
    (Finset.sum_le_card_nsmul _ _ ε fun k _ ↦ hstep _).trans_eq (by simp [nsmul_eq_mul])

end MultiQueryHybridLift

end AsymmEncAlg
