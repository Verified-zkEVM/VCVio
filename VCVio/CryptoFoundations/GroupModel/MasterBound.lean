/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Collision
public import VCVio.CryptoFoundations.GroupModel.Cost
public import VCVio.CryptoFoundations.GroupModel.Instances
public import VCVio.OracleComp.Constructions.SampleableType.SchwartzZippel
public import VCVio.EvalDist.MeasureTVDist.Bind
public import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.List.GetD

/-!
Polynomial group models: degree invariants and the master bound

Equality under evaluation at a hidden point is compared with exact polynomial equality.
Zero defaults for out-of-range handles are included in the collision event.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace GroupModel

variable {F S ι : Type}

/-! ## Degree invariants -/

/-- Every polynomial stored in the table has total degree at most `d`. -/
@[expose] def DegreeLE [CommSemiring F] (d : ℕ) (tbl : Tbl (fun _ : S => MvPolynomial ι F)) :
    Prop := ∀ s p, p ∈ tbl s → p.totalDegree ≤ d

private theorem lookup_mem [Zero F] (tbl : Tbl (fun _ : S => F)) (s : S) (a : Handle) :
    lookup tbl s a ∈ tbl s ++ [0] := by
  by_cases h : a < (tbl s).length
  · simp only [lookup, List.getD_eq_getElem _ _ h, List.mem_append, List.mem_singleton]
    exact Or.inl (List.getElem_mem h)
  · rw [lookup, List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    simp

/-- Reading a degree-bounded table, including the zero default, preserves the bound. -/
theorem DegreeLE.lookup [CommSemiring F] {d : ℕ} {tbl : Tbl (fun _ : S => MvPolynomial ι F)}
    (h : DegreeLE d tbl) (s : S) (a : Handle) : (lookup tbl s a).totalDegree ≤ d := by
  have hm := lookup_mem tbl s a
  simp only [List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | hm
  · exact h s _ hm
  · simp [hm]

private theorem degreeLE_append [CommSemiring F] [DecidableEq S] {d : ℕ}
    {tbl : Tbl (fun _ : S => MvPolynomial ι F)} (h : DegreeLE d tbl)
    (s : S) (p : MvPolynomial ι F) (hp : p.totalDegree ≤ d) : DegreeLE d (append tbl s p) := by
  intro t v hv
  by_cases ht : t = s
  · subst t
    simp only [append, Function.update_self, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact h s v hv
    · exact hp
  · exact h t v (by simpa [append, ht] using hv)

/-- One discrete symbolic group query preserves the degree bound, for any observation. -/
theorem impl_degreeLE [CommSemiring F] [DecidableEq S]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (obs : (s : S) → MvPolynomial ι F → U s) (t : Query F (discreteSig S))
    {d : ℕ} (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (htbl : DegreeLE d tbl)
    (z : spec F (discreteSig S) t × Tbl (fun _ : S => MvPolynomial ι F))
    (hz : z ∈ support ((impl (symbolic F (discreteSig S) ι) obs ProbComp t).run tbl)) :
    DegreeLE d z.2 := by
  cases t with
  | add s a b =>
    simp only [impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet] at hz
    subst z
    exact degreeLE_append htbl s _ ((MvPolynomial.totalDegree_add _ _).trans
      (max_le (htbl.lookup s a) (htbl.lookup s b)))
  | smul s c a =>
    simp only [impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet] at hz
    subst z
    exact degreeLE_append htbl s _ ((MvPolynomial.totalDegree_smul_le c _).trans
      (htbl.lookup s a))
  | eq s a b =>
    have h := impl_table_step (symbolic F (discreteSig S) ι) obs (.eq s a b) tbl z hz
    have he : z.2 = tbl := h
    simpa only [he] using htbl
  | lin o a => exact o.elim
  | bil o a b => exact o.elim

/-- Every reachable table of a discrete symbolic generic run has the initial degree bound. -/
theorem runGen_degreeLE [CommSemiring F] [DecidableEq S]
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (obs : (s : S) → MvPolynomial ι F → U s) {α : Type}
    (oa : OracleComp (genSpec F (discreteSig S)) α)
    {d : ℕ} (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (htbl : DegreeLE d tbl)
    (z : α × Tbl (fun _ : S => MvPolynomial ι F))
    (hz : z ∈ support (runGen (symbolic F (discreteSig S) ι) obs oa tbl)) :
    DegreeLE d z.2 := by
  induction oa using OracleComp.inductionOn generalizing tbl with
  | pure a =>
    simp only [runGen, run, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst z
    exact htbl
  | query_bind t k ih =>
    simp only [runGen, run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    apply ih w.1 w.2 _ hz
    cases t with
    | inl t => exact impl_degreeLE obs t tbl htbl w hw
    | inr t => simpa only [preservesTbl_coins t tbl w hw] using htbl

/-! ## Collisions in the final table -/

/-- A table collision includes distinct entries or the zero default in one sort. -/
@[expose] def TableCollision [Zero F] (obs : S → F → ι) (tbl : Tbl (fun _ : S => F)) : Prop :=
  ∃ s p, p ∈ tbl s ++ [0] ∧ ∃ q, q ∈ tbl s ++ [0] ∧ p ≠ q ∧ obs s p = obs s q

private theorem tableCollision_mono [Zero F] {obs : S → F → ι}
    {tbl tbl' : Tbl (fun _ : S => F)} (hp : ∀ s, tbl s <+: tbl' s)
    (h : TableCollision obs tbl) : TableCollision obs tbl' := by
  obtain ⟨s, p, hp', q, hq, hne, he⟩ := h
  refine ⟨s, p, ?_, q, ?_, hne, he⟩
  all_goals
    rw [List.mem_append] at *
    exact Or.imp (fun h => (hp s).subset h) id (by assumption)

private theorem isCollision_tableCollision [Zero F] {σ : Sig S}
    {K : Type} {obs : S → F → ι} {tbl : Tbl (fun _ : S => F)} {t : Query K σ}
    (h : IsCollision obs tbl t) : TableCollision obs tbl := by
  cases t with
  | eq s a b => exact ⟨s, _, lookup_mem tbl s a, _, lookup_mem tbl s b, h⟩
  | _ => exact h.elim

private theorem runFlag_tableCollision {K A B : Type} [CommSemiring K] [DecidableEq S]
    [AddCommMonoid A] [Module K A] [DecidableEq A] [DecidableEq B] {σ : Sig S}
    (M : Model K σ (fun _ => A)) (obs : S → A → B) {α : Type}
    (oa : OracleComp (genSpec K σ) α) (st : Tbl (fun _ : S => A) × Bool)
    (hst : st.2 = true → TableCollision obs st.1)
    (z : α × Tbl (fun _ : S => A) × Bool)
    (hz : z ∈ support (runFlag M obs (fun _ => id)
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tbl (fun _ : S => A)) ProbComp))
      oa st)) : z.2.2 = true → TableCollision obs z.2.1 := by
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [runFlag, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst z
    exact hst
  | query_bind t k ih =>
    simp only [runFlag, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    apply ih w.1 w.2 _ hz
    cases t with
    | inl t =>
      simp only [QueryImpl.add_apply_inl, flagHandler,
        QueryImpl.mem_support_extendState_run_iff] at hw
      intro hb
      have hp := impl_prefix M (fun _ => id) t st.1 (w.1, w.2.1) hw.1
      apply tableCollision_mono hp
      rw [hw.2, Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · exact hst hb
      · exact isCollision_tableCollision (of_decide_eq_true hb)
    | inr t =>
      simp only [QueryImpl.add_apply_inr, liftGameFlag,
        QueryImpl.mem_support_extendState_run_iff] at hw
      intro hb
      have he : w.2.1 = st.1 := preservesTbl_coins t st.1 (w.1, w.2.1) hw.1
      rw [he]
      exact hst (hw.2 ▸ hb)

/-- A collision during exact comparison implies a collision among final entries and zero.
This bound includes equality queries whose handles are out of range. -/
theorem collisionProbGen_le_tableCollision {K A B : Type} [CommSemiring K] [DecidableEq S]
    [AddCommMonoid A] [Module K A] [DecidableEq A] [DecidableEq B] {σ : Sig S}
    (M : Model K σ (fun _ => A)) (obs : S → A → B) {α : Type}
    (oa : OracleComp (genSpec K σ) α) (tbl : Tbl (fun _ : S => A)) :
    collisionProbGen M obs oa tbl ≤
      Pr{let z ← runGen M (fun _ => id) oa tbl}[TableCollision obs z.2] := by
  let game := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (Tbl (fun _ : S => A)) ProbComp)
  change Pr{let z ← runFlag M obs (fun _ => id) game oa (tbl, false)}[z.2.2 = true] ≤ _
  have h := prEvent_mono_of_support (runFlag M obs (fun _ => id) game oa (tbl, false))
    (fun z => z.2.2 = true) (fun z => TableCollision obs z.2.1)
    (fun z hz => runFlag_tableCollision M obs oa (tbl, false) (by simp) z hz)
  have he := runFlag_project M obs (fun _ => id) game oa (tbl, false)
  change Prod.map id Prod.fst <$> runFlag M obs (fun _ => id) game oa (tbl, false) =
    runGen M (fun _ => id) oa tbl at he
  rw [← he]
  simpa only [Functor.map_map, Function.comp_def, Prod.map] using h

/-! ## Counting polynomial collisions -/

private def ListCollision [CommSemiring F] (ps : List (MvPolynomial ι F)) (x : ι → F) :
    Prop := ∃ p ∈ ps, ∃ q ∈ ps, p ≠ q ∧ MvPolynomial.eval x p = MvPolynomial.eval x q

private theorem pair_collision_le [Field F] (xs : ProbComp (ι → F)) {d : ℕ} {ε : ℝ≥0∞}
    (hε : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε)
    (p q : MvPolynomial ι F) (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    Pr{let x ← xs}[p ≠ q ∧ MvPolynomial.eval x p = MvPolynomial.eval x q] ≤ ε := by
  by_cases h : p = q
  · simp [h]
  · apply (prEvent_mono xs _ (fun x => MvPolynomial.eval x (p - q) = 0) ?_).trans
      (hε (p - q) (sub_ne_zero.mpr h) ((MvPolynomial.totalDegree_sub _ _).trans
        (max_le hp hq)))
    intro x hx
    simpa only [map_sub, sub_eq_zero] using hx.2

private theorem list_collision_le [Field F] (xs : ProbComp (ι → F)) {d : ℕ} {ε : ℝ≥0∞}
    (hε : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε)
    (ps : List (MvPolynomial ι F)) (hd : ∀ p ∈ ps, p.totalDegree ≤ d) :
    Pr{let x ← xs}[ListCollision ps x] ≤ (ps.length.choose 2 : ℝ≥0∞) * ε := by
  classical
  induction ps with
  | nil =>
    rw [prEvent_eq_zero_of_forall_not xs _ (by simp [ListCollision])]
    exact zero_le
  | cons p ps ih =>
    have hu : Pr{let x ← xs}[∃ q ∈ ps, p ≠ q ∧
        MvPolynomial.eval x p = MvPolynomial.eval x q] ≤ (ps.length : ℝ≥0∞) * ε := by
      have h := prEvent_exists_finset_le_card_mul ps.toFinset xs
        (fun q x => p ≠ q ∧ MvPolynomial.eval x p = MvPolynomial.eval x q)
        (fun q hq => pair_collision_le xs hε p q (hd p (by simp))
          (hd q (List.mem_cons_of_mem p (List.mem_toFinset.mp hq))))
      simp only [List.mem_toFinset] at h
      apply h.trans
      gcongr
      exact List.toFinset_card_le ps
    have hm : Pr{let x ← xs}[ListCollision (p :: ps) x] ≤
        Pr{let x ← xs}[(∃ q ∈ ps, p ≠ q ∧
          MvPolynomial.eval x p = MvPolynomial.eval x q) ∨ ListCollision ps x] := by
      apply prEvent_mono
      intro x hx
      obtain ⟨a, ha, b, hb, hn, he⟩ := hx
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact (hn rfl).elim
        · exact Or.inl ⟨b, hb, hn, he⟩
      · rcases hb with rfl | hb
        · exact Or.inl ⟨a, ha, Ne.symm hn, he.symm⟩
        · exact Or.inr ⟨a, ha, b, hb, hn, he⟩
    refine (hm.trans (prEvent_or_le xs _ _)).trans ?_
    have hi := ih (fun q hq => hd q (List.mem_cons_of_mem p hq))
    calc
      _ ≤ (ps.length : ℝ≥0∞) * ε + (ps.length.choose 2 : ℝ≥0∞) * ε := add_le_add hu hi
      _ = _ := by rw [List.length_cons, Nat.choose_succ_succ, Nat.choose_one_right,
        Nat.cast_add, add_mul]

/-- A root-probability bound controls collisions among all table entries and the zero default.
The count uses the total number of entries across sorts. -/
theorem tableCollision_prob_le [Field F] [Fintype S]
    (xs : ProbComp (ι → F)) {d : ℕ} {ε : ℝ≥0∞}
    (hε : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE d tbl) :
    Pr{let x ← xs}[TableCollision (fun _ p => MvPolynomial.eval x p) tbl] ≤
      (((∑ s, (tbl s).length) + 1).choose 2 : ℝ≥0∞) * ε := by
  classical
  let ps := Finset.univ.toList.flatMap tbl ++ [0]
  have hm (s : S) (p : MvPolynomial ι F) (hp : p ∈ tbl s ++ [0]) : p ∈ ps := by
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, by simp, hp⟩)
    · simp [ps]
  have hd' : ∀ p ∈ ps, p.totalDegree ≤ d := by
    intro p hp
    simp only [ps, List.mem_append, List.mem_flatMap, Finset.mem_toList,
      Finset.mem_univ, true_and, List.mem_singleton] at hp
    rcases hp with ⟨s, hp⟩ | rfl
    · exact hd s p hp
    · simp
  have hl : ps.length = (∑ s, (tbl s).length) + 1 := by
    simp [ps, List.length_flatMap, Finset.sum_map_toList]
  calc
    _ ≤ Pr{let x ← xs}[ListCollision ps x] := prEvent_mono xs _ _ (by
      intro x hx
      obtain ⟨s, p, hp, q, hq, hn, he⟩ := hx
      exact ⟨p, hm s p hp, q, hm s q hq, hn, he⟩)
    _ ≤ _ := by simpa only [hl] using list_collision_le xs hε ps hd'

/-! ## Joint total variation and event bounds -/

/-- **T3, the master bound.** Evaluated and exact equality differ in total variation by at
most `choose (initial size + operation budget + 1) 2 * ε`, jointly with the hidden point and
full output/table pair. The joint output may carry any measurable space; the proof uses
local discrete spaces on the point and intermediate table outputs. -/
theorem measureETVDist_runGen_symbolic_le [Field F] [DecidableEq F] [DecidableEq ι]
    [Fintype S] [DecidableEq S] {α : Type}
    [MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F)))]
    (xs : ProbComp (ι → F)) {d q : ℕ} {ε : ℝ≥0∞}
    (hε : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε)
    (oa : OracleComp (genSpec F (discreteSig S)) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE d tbl) :
    measureETVDist
      (do let x ← xs
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z))
      (do let x ← xs
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ => id) oa tbl
          pure (x, z)) ≤
      (((∑ s, (tbl s).length) + q + 1).choose 2 : ℝ≥0∞) * ε := by
  let : MeasurableSpace (ι → F) := ⊤
  let : MeasurableSpace (α × Tbl (fun _ : S => MvPolynomial ι F)) := ⊤
  let M := symbolic F (discreteSig S) ι
  let exactRun := runGen M (fun _ => id) oa tbl
  let bad := fun x (z : α × Tbl (fun _ : S => MvPolynomial ι F)) =>
    TableCollision (fun _ p => MvPolynomial.eval x p) z.2
  have hpoint (x : ι → F) :
      measureETVDist
        ((fun z => (x, z)) <$> runGen M (fun _ p => MvPolynomial.eval x p) oa tbl)
        ((fun z => (x, z)) <$> exactRun) ≤ Pr{let z ← exactRun}[bad x z] :=
    (measureETVDist_map_le _ _ _ Measurable.of_discrete).trans
      ((measureETVDist_runGen_le_collisionProbGen M _ oa tbl).trans
        (collisionProbGen_le_tableCollision M _ oa tbl))
  have hmix := measureETVDist_bind_bind_le_lintegral xs
    (fun x => (fun z => (x, z)) <$> runGen M (fun _ p => MvPolynomial.eval x p) oa tbl)
    (fun x => (fun z => (x, z)) <$> exactRun)
    Measurable.of_discrete Measurable.of_discrete
    (fun x => Pr{let z ← exactRun}[bad x z]) (Filter.Eventually.of_forall hpoint)
  simp only [bind_pure_comp]
  refine hmix.trans ?_
  rw [← prEvent_bind_bind_eq_lintegral_of_discrete xs (fun _ => exactRun) bad,
    prEvent_bind_map_swap]
  have hbnd := prEvent_bind_le_of_forall_le_of_support exactRun
    (fun z => (fun x => bad x z) <$> xs) id (ε :=
      (((∑ s, (tbl s).length) + q + 1).choose 2 : ℝ≥0∞) * ε) (by
    intro z hz
    have hzdeg := runGen_degreeLE (fun _ => id) oa tbl hd z hz
    have hzsize := runGen_sum_length_le M (fun _ => id) hq tbl z hz
    have hb := tableCollision_prob_le xs hε z.2 hzdeg
    simp only [Functor.map_map, id_eq]
    apply hb.trans
    gcongr)
  simpa only [map_bind, id_map] using hbnd

/-- Every measurable event on the hidden point and full run output satisfies the master
bound in both directions. -/
theorem prEvent_runGen_symbolic_le_add [Field F] [DecidableEq F] [DecidableEq ι]
    [Fintype S] [DecidableEq S] {α : Type}
    [MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F)))]
    (xs : ProbComp (ι → F)) {d q : ℕ} {ε : ℝ≥0∞}
    (hε : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ d →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε)
    (oa : OracleComp (genSpec F (discreteSig S)) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE d tbl)
    (E : Set ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F))))
    (hE : MeasurableSet E) :
    (Pr{let x ← xs; let z ← (runGen (symbolic F (discreteSig S) ι)
          (fun _ p => MvPolynomial.eval x p) oa tbl)}[
          (x, z) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F (discreteSig S) ι)
          (fun _ => id) oa tbl)}[(x, z) ∈ E] +
      (((∑ s, (tbl s).length) + q + 1).choose 2 : ℝ≥0∞) * ε) ∧
    (Pr{let x ← xs; let z ← (runGen (symbolic F (discreteSig S) ι)
          (fun _ => id) oa tbl)}[(x, z) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F (discreteSig S) ι)
          (fun _ p => MvPolynomial.eval x p) oa tbl)}[
          (x, z) ∈ E] +
      (((∑ s, (tbl s).length) + q + 1).choose 2 : ℝ≥0∞) * ε) := by
  let left : ProbComp ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F))) := do
    let x ← xs
    let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa tbl
    pure (x, z)
  let right : ProbComp ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F))) := do
    let x ← xs
    let z ← runGen (symbolic F (discreteSig S) ι) (fun _ => id) oa tbl
    pure (x, z)
  have h : measureETVDist left right ≤ _ := measureETVDist_runGen_symbolic_le xs hε oa hq tbl hd
  have hl := (prEvent_le_prEvent_add_measureETVDist left right (· ∈ E) hE.mem).trans
    (add_le_add le_rfl h)
  rw [measureETVDist_comm] at h
  have hr := (prEvent_le_prEvent_add_measureETVDist right left (· ∈ E) hE.mem).trans
    (add_le_add le_rfl h)
  simpa only [left, right, map_bind, map_pure, bind_pure_comp, Functor.map_map,
    Function.comp_def] using And.intro hl hr

/-- Uniform hidden points over a finite field give the Schwartz–Zippel specialization
`choose (initial size + operation budget + 1) 2 * (d / card F)` of the joint master bound. -/
theorem measureETVDist_runGen_symbolic_uniform_le [Field F] [DecidableEq F]
    [Fintype F] [SampleableType F] [Finite ι] [DecidableEq ι]
    [SampleableType (ι → F)]
    [Fintype S] [DecidableEq S] {α : Type}
    [MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F)))]
    {d q : ℕ} (oa : OracleComp (genSpec F (discreteSig S)) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE d tbl) :
    measureETVDist
      (do let x ← $ᵗ (ι → F)
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z))
      (do let x ← $ᵗ (ι → F)
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ => id) oa tbl
          pure (x, z)) ≤
      (((∑ s, (tbl s).length) + q + 1).choose 2 : ℝ≥0∞) *
        ((d : ℝ≥0∞) / Fintype.card F) := by
  apply measureETVDist_runGen_symbolic_le ($ᵗ (ι → F)) _ oa hq tbl hd
  intro f hf hdeg
  let : Fintype ι := Fintype.ofFinite ι
  rw [SampleableType.prEvent_uniformSample_inst_irrel
    (inferInstance : SampleableType (ι → F)) instSampleableTypePiFintype]
  exact prob_eval_zero_univ_le_div f hf hdeg

end GroupModel
