/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.CostModel
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Weighted costs and adaptive resource tradeoffs

Structural bounds control the weighted cost of free oracle programs. An adaptive client
separates the maxima of two kinds of queries while retaining a smaller joint cost bound.
The original cost facade supplies erasure and almost-sure interpretations.
-/

public section

open OracleComp OracleSpec
namespace RefactorProbe

/-- A structural weighted budget controls the same exact weighted observation. -/
theorem weighted_of_structural {ι α : Type} {spec : OracleSpec ι}
    (p : OracleComp spec α) (cm : CostModel spec Nat) (budget : Nat)
    (h : IsQueryBound p budget (fun t b => cm.queryCost t ≤ b)
      (fun t b => b - cm.queryCost t)) :
    WorstCaseCostBound p cm budget := by
  induction p using OracleComp.inductionOn generalizing budget with
  | pure x => simp
  | query_bind t next ih =>
    rw [isQueryBound_query_bind_iff] at h
    rw [worstCaseCostBound_query_bind_iff]
    intro u z hz
    have hr := (worstCaseCostBound_iff_support_bound _ _ _).mp
      (ih u (budget - cm.queryCost t) (h.2 u)) z hz
    omega

/-- A uniform per-query upper charge transports a structural total bound to weighted cost. -/
theorem weighted_of_total {ι α : Type} {spec : OracleSpec ι}
    (p : OracleComp spec α) (cm : CostModel spec Nat) (n cap : Nat)
    (h : IsTotalQueryBound p n) (hc : ∀ t, cm.queryCost t ≤ cap) :
    WorstCaseCostBound p cm (n * cap) := by
  induction p using OracleComp.inductionOn generalizing n with
  | pure x => simp
  | query_bind t next ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [worstCaseCostBound_query_bind_iff]
    intro u z hz
    have hr := (worstCaseCostBound_iff_support_bound _ _ _).mp (ih u (n - 1) (h.2 u)) z hz
    have hn : n - 1 + 1 = n := by omega
    calc cm.queryCost t + Multiplicative.toAdd z.2 ≤ cap + (n - 1) * cap := Nat.add_le_add (hc t) hr
         _ = (n - 1 + 1) * cap := by simp [Nat.add_mul, Nat.add_comm]
         _ = n * cap := by rw [hn]

abbrev Spec : OracleSpec (Fin 3) := Fin 3 →ₒ Bool

def ask (i : Fin 3) : OracleComp Spec Bool := liftM (Spec.query i)

/-- Index0 is control traffic, index1 hashes, index2 signing requests. -/
def adaptive : OracleComp Spec Bool := do
  let branch ← ask 0
  if branch then
    let _ ← ask 1
    ask 1
  else
    let _ ← ask 2
    ask 2

def joint : CostModel Spec Nat := ⟨fun i => if i = 0 then 0 else 1⟩
def hashOnly : CostModel Spec Nat := ⟨fun i => if i = 1 then 1 else 0⟩
def signOnly : CostModel Spec Nat := ⟨fun i => if i = 2 then 1 else 0⟩
def weighted : CostModel Spec Nat := ⟨fun i => if i = 0 then 0 else if i = 1 then 3 else 1⟩

theorem ask_total (i : Fin 3) : IsTotalQueryBound (ask i) 1 := by
  change IsTotalQueryBound ((liftM (Spec.query i)) >>= pure) 1
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => trivial⟩

theorem adaptive_total : IsTotalQueryBound adaptive 3 := by
  simp only [adaptive, ask, isTotalQueryBound_query_bind_iff]
  constructor
  · decide
  · intro b; cases b
    · change IsTotalQueryBound ((ask 2) >>= fun _ => ask 2) 2
      rw [ask, isTotalQueryBound_query_bind_iff]
      exact ⟨by decide, fun _ => ask_total 2⟩
    · change IsTotalQueryBound ((ask 1) >>= fun _ => ask 1) 2
      rw [ask, isTotalQueryBound_query_bind_iff]
      exact ⟨by decide, fun _ => ask_total 1⟩

theorem adaptive_joint : WorstCaseCostBound adaptive joint 2 := by
  simp only [adaptive, ask, worstCaseCostBound_query_bind_iff]
  intro b z hz
  cases b <;> simp [joint, costDist, instrumentedRun,
    QueryImpl.withAddCost, WriterT.run_bind, bind_assoc] at hz ⊢ <;> aesop

theorem adaptive_weighted_structural : IsQueryBound adaptive 6
    (fun t b => weighted.queryCost t ≤ b) (fun t b => b - weighted.queryCost t) := by
  simp only [adaptive, ask, isQueryBound_query_bind_iff]
  constructor
  · decide
  · intro b; cases b <;>
      simp [weighted, isQueryBound_query_bind_iff, isQueryBound_query_iff]

theorem adaptive_weighted : WorstCaseCostBound adaptive weighted 6 :=
  weighted_of_structural _ _ _ adaptive_weighted_structural

theorem weighted_six_reachable : (false, Multiplicative.ofAdd 6) ∈
    support (costDist adaptive weighted) := by
  simp [adaptive, ask, weighted, costDist, instrumentedRun, QueryImpl.withAddCost,
    WriterT.run_bind, bind_assoc]
  have h (i : Fin 3) (b : Bool) : MonadAttach.CanReturn (ask i) b := by
    change b ∈ support (ask i)
    simp [ask]
  exact Or.inr ⟨Or.inl (h 1 false), h 1 false, rfl⟩

theorem adaptive_hash : IsQueryBoundP adaptive (fun i => i = 1) 2 := by
  simp only [adaptive, ask, isQueryBoundP_query_bind_iff]
  constructor
  · simp
  · intro b; cases b <;> simp [isQueryBoundP_query_bind_iff, isQueryBoundP_query_iff]

theorem adaptive_sign : IsQueryBoundP adaptive (fun i => i = 2) 2 := by
  simp only [adaptive, ask, isQueryBoundP_query_bind_iff]
  constructor
  · simp
  · intro b; cases b <;> simp [isQueryBoundP_query_bind_iff, isQueryBoundP_query_iff]

theorem hash_two_reachable : (false, Multiplicative.ofAdd 2) ∈
    support (costDist adaptive hashOnly) := by
  simp [adaptive, ask, hashOnly, costDist, instrumentedRun, QueryImpl.withAddCost,
    WriterT.run_bind, bind_assoc]
  have h (i : Fin 3) (b : Bool) : MonadAttach.CanReturn (ask i) b := by
    change b ∈ support (ask i)
    simp [ask]
  exact Or.inr ⟨Or.inl (h 1 false), h 1 false, rfl⟩

theorem sign_two_reachable : (false, Multiplicative.ofAdd 2) ∈
    support (costDist adaptive signOnly) := by
  simp [adaptive, ask, signOnly, costDist, instrumentedRun, QueryImpl.withAddCost,
    WriterT.run_bind, bind_assoc]
  have h (i : Fin 3) (b : Bool) : MonadAttach.CanReturn (ask i) b := by
    change b ∈ support (ask i)
    simp [ask]
  exact Or.inl ⟨Or.inl (h 2 false), h 2 false, rfl⟩

theorem separate_hash_needs_two {n : Nat} (h : WorstCaseCostBound adaptive hashOnly n) : 2 ≤ n :=
  (worstCaseCostBound_iff_support_bound _ _ _).mp h _ hash_two_reachable

theorem separate_sign_needs_two {n : Nat} (h : WorstCaseCostBound adaptive signOnly n) : 2 ≤ n :=
  (worstCaseCostBound_iff_support_bound _ _ _).mp h _ sign_two_reachable

theorem adaptive_erasure : Prod.fst <$> costDist adaptive joint = adaptive :=
  fst_map_costDist _ _

theorem adaptive_joint_ae [AnswerMeasure Spec] :
    AddWriterT.AECostAtMost (instrumentedRun adaptive joint) 2 :=
  AddWriterT.aeCostAtMost_of_pathwiseCostAtMost adaptive_joint (by measurability)

theorem adaptive_joint_p1 [UniformAnswerMeasure Spec] :
    Pr{let result ← costDist adaptive joint}[Multiplicative.toAdd result.2 ≤ 2] = 1 := by
  exact prEvent_eq_one_of_forall_mem_support _ _
    ((worstCaseCostBound_iff_support_bound _ _ _).mp adaptive_joint)

#print axioms weighted_of_structural
#print axioms adaptive_weighted
#print axioms weighted_six_reachable
#print axioms adaptive_total
#print axioms weighted_of_total
#print axioms adaptive_joint
#print axioms adaptive_hash
#print axioms adaptive_sign
#print axioms separate_hash_needs_two
#print axioms separate_sign_needs_two
#print axioms adaptive_erasure
#print axioms adaptive_joint_ae
#print axioms adaptive_joint_p1
end RefactorProbe
