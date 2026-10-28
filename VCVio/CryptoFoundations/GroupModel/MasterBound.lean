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

/-- The degree bounds are preserved by every linear and bilinear structure map. -/
@[expose] def Sig.DegreeClosed (σ : Sig S) (D : S → ℕ) : Prop :=
  (∀ o, D (σ.lsrc o) ≤ D (σ.ltgt o)) ∧
    (∀ o, D (σ.src₁ o) + D (σ.src₂ o) ≤ D (σ.tgt o))

/-- Independent sorts allow every choice of degree bounds. -/
theorem degreeClosed_discreteSig (D : S → ℕ) : (discreteSig S).DegreeClosed D :=
  ⟨fun o => o.elim, fun o => o.elim⟩

/-- The least closed Type 3 bounds extend the target bound by the sum of source bounds. -/
theorem degreeClosed_pairingSig (d₁ d₂ dₜ : ℕ) :
    pairingSig.DegreeClosed (fun | .g₁ => d₁ | .g₂ => d₂ | .gₜ => max dₜ (d₁ + d₂)) :=
  ⟨fun o => o.elim, fun _ => Nat.le_max_right _ _⟩

/-- Every polynomial stored in the table has total degree at most `D s` in sort `s`. -/
@[expose] def DegreeLE [CommSemiring F] (D : S → ℕ) (tbl : Tbl (fun _ : S => MvPolynomial ι F)) :
    Prop := ∀ s p, p ∈ tbl s → p.totalDegree ≤ D s

private theorem lookup_mem [Zero F] (tbl : Tbl (fun _ : S => F)) (s : S) (a : Handle) :
    lookup tbl s a ∈ tbl s ++ [0] := by
  by_cases h : a < (tbl s).length
  · simp only [lookup, List.getD_eq_getElem _ _ h, List.mem_append, List.mem_singleton]
    exact Or.inl (List.getElem_mem h)
  · rw [lookup, List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    simp

/-- Reading a degree-bounded table, including the zero default, preserves the bound. -/
theorem DegreeLE.lookup [CommSemiring F] {D : S → ℕ} {tbl : Tbl (fun _ : S => MvPolynomial ι F)}
    (h : DegreeLE D tbl) (s : S) (a : Handle) : (lookup tbl s a).totalDegree ≤ D s := by
  have hm := lookup_mem tbl s a
  simp only [List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | hm
  · exact h s _ hm
  · simp [hm]

private theorem degreeLE_append [CommSemiring F] [DecidableEq S] {D : S → ℕ}
    {tbl : Tbl (fun _ : S => MvPolynomial ι F)} (h : DegreeLE D tbl)
    (s : S) (p : MvPolynomial ι F) (hp : p.totalDegree ≤ D s) : DegreeLE D (append tbl s p) := by
  intro t v hv
  by_cases ht : t = s
  · subst t
    simp only [append, Function.update_self, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact h s v hv
    · exact hp
  · exact h t v (by simpa [append, ht] using hv)

/-- One symbolic group query preserves the degree bound, for any observation. -/
theorem impl_degreeLE [CommSemiring F] [DecidableEq S]
    {σ : Sig S} {D : S → ℕ} (hD : σ.DegreeClosed D)
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (obs : (s : S) → MvPolynomial ι F → U s) (t : Query F σ)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (htbl : DegreeLE D tbl)
    (z : spec F σ t × Tbl (fun _ : S => MvPolynomial ι F))
    (hz : z ∈ support ((impl (symbolic F σ ι) obs ProbComp t).run tbl)) :
    DegreeLE D z.2 := by
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
    have h := impl_table_step (symbolic F σ ι) obs (.eq s a b) tbl z hz
    have he : z.2 = tbl := h
    simpa only [he] using htbl
  | lin o a =>
    simp only [impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet] at hz
    subst z
    apply degreeLE_append htbl (σ.ltgt o)
    simpa only [symbolic_lin_apply] using (htbl.lookup (σ.lsrc o) a).trans (hD.1 o)
  | bil o a b =>
    simp only [impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet] at hz
    subst z
    apply degreeLE_append htbl (σ.tgt o)
    simp only [symbolic_bil_apply]
    exact (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add (htbl.lookup (σ.src₁ o) a) (htbl.lookup (σ.src₂ o) b)).trans (hD.2 o))

/-- Every reachable table of a symbolic generic run has the initial degree bound. -/
theorem runGen_degreeLE [CommSemiring F] [DecidableEq S]
    {σ : Sig S} {D : S → ℕ} (hD : σ.DegreeClosed D)
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (obs : (s : S) → MvPolynomial ι F → U s) {α : Type}
    (oa : OracleComp (genSpec F σ) α)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (htbl : DegreeLE D tbl)
    (z : α × Tbl (fun _ : S => MvPolynomial ι F))
    (hz : z ∈ support (runGen (symbolic F σ ι) obs oa tbl)) :
    DegreeLE D z.2 := by
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
    | inl t => exact impl_degreeLE hD obs t tbl htbl w hw
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

/-- A root bound for each sort controls collisions among its entries and its zero default. -/
theorem tableCollision_prob_le [Field F] [Fintype S]
    (xs : ProbComp (ι → F)) {D : S → ℕ} {ε : S → ℝ≥0∞}
    (hε : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε s)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE D tbl) :
    Pr{let x ← xs}[TableCollision (fun _ p => MvPolynomial.eval x p) tbl] ≤
      ∑ s, (((tbl s).length + 1).choose 2 : ℝ≥0∞) * ε s := by
  apply (prEvent_exists_le xs (fun s x => ListCollision (tbl s ++ [0]) x)).trans
  apply Finset.sum_le_sum
  intro s _
  have hdeg : ∀ p ∈ tbl s ++ [0], p.totalDegree ≤ D s := by
    intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hd s p hp
    · simp
  simpa only [List.length_append, List.length_singleton] using
    list_collision_le xs (hε s) (tbl s ++ [0]) hdeg

private theorem sum_choose_succ_le (m : S → ℕ) (t : Finset S) :
    ∑ s ∈ t, (m s + 1).choose 2 ≤ ((∑ s ∈ t, m s) + 1).choose 2 := by
  classical
  have hadd (a b : ℕ) :
      (a + 1).choose 2 + (b + 1).choose 2 ≤ (a + b + 1).choose 2 := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Nat.choose_succ_succ (b + 1) 1,
        Nat.choose_one_right]
      rw [show a + (b + 1) + 1 = (a + b + 1) + 1 by omega,
        Nat.choose_succ_succ (a + b + 1) 1, Nat.choose_one_right]
      simp only [Nat.reduceSucc] at *
      omega
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (Nat.add_le_add_left ih _).trans (hadd _ _)

/-! ## Joint total variation and event bounds -/

/-- **T3ₛ.** A bound on the sorted collision sum of every exact output bounds joint total
variation, including the hidden point and the full output table. -/
theorem measureETVDist_runGen_symbolic_le_of_support [Field F] [DecidableEq F] [DecidableEq ι]
    [Fintype S] [DecidableEq S] {α : Type} {σ : Sig S}
    [MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F)))]
    (xs : ProbComp (ι → F)) {D : S → ℕ} {ε : S → ℝ≥0∞} {B : ℝ≥0∞}
    (hD : σ.DegreeClosed D)
    (hε : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε s)
    (oa : OracleComp (genSpec F σ) α)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE D tbl)
    (hB : ∀ z ∈ support (runGen (symbolic F σ ι) (fun _ => id) oa tbl),
      ∑ s, (((z.2 s).length + 1).choose 2 : ℝ≥0∞) * ε s ≤ B) :
    measureETVDist
      (do let x ← xs
          let z ← runGen (symbolic F σ ι) (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z))
      (do let x ← xs
          let z ← runGen (symbolic F σ ι) (fun _ => id) oa tbl
          pure (x, z)) ≤
      B := by
  let : MeasurableSpace (ι → F) := ⊤
  let : MeasurableSpace (α × Tbl (fun _ : S => MvPolynomial ι F)) := ⊤
  let M := symbolic F σ ι
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
      B) (by
    intro z hz
    have hzdeg := runGen_degreeLE hD (fun _ => id) oa tbl hd z hz
    have hb := tableCollision_prob_le xs hε z.2 hzdeg
    simp only [Functor.map_map, id_eq]
    exact hb.trans (hB z hz))
  simpa only [map_bind, id_map] using hbnd

/-- **T3ₛ.** Per-sort operation budgets bound joint total variation with the hidden point
and the full output table. -/
theorem measureETVDist_runGen_symbolic_le_of_target [Field F] [DecidableEq F] [DecidableEq ι]
    [Fintype S] [DecidableEq S] {α : Type} {σ : Sig S}
    [MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F)))]
    (xs : ProbComp (ι → F)) {D : S → ℕ} {ε : S → ℝ≥0∞} {n : S → ℕ}
    (hD : σ.DegreeClosed D)
    (hε : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε s)
    (oa : OracleComp (genSpec F σ) α)
    (hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s))
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE D tbl) :
    measureETVDist
      (do let x ← xs
          let z ← runGen (symbolic F σ ι) (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z))
      (do let x ← xs
          let z ← runGen (symbolic F σ ι) (fun _ => id) oa tbl
          pure (x, z)) ≤
      ∑ s, (((tbl s).length + n s + 1).choose 2 : ℝ≥0∞) * ε s := by
  apply measureETVDist_runGen_symbolic_le_of_support xs hD hε oa tbl hd
  intro z hz
  apply Finset.sum_le_sum
  intro s _
  have hs := runGen_length_le_of_target (symbolic F σ ι) (fun _ => id) s (hn s) tbl z hz
  gcongr

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
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE (fun _ => d) tbl) :
    measureETVDist
      (do let x ← xs
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ p => MvPolynomial.eval x p) oa tbl
          pure (x, z))
      (do let x ← xs
          let z ← runGen (symbolic F (discreteSig S) ι) (fun _ => id) oa tbl
          pure (x, z)) ≤
      (((∑ s, (tbl s).length) + q + 1).choose 2 : ℝ≥0∞) * ε := by
  apply measureETVDist_runGen_symbolic_le_of_support xs (degreeClosed_discreteSig _)
    (fun _ => hε) oa tbl hd
  intro z hz
  rw [← Finset.sum_mul]
  have hc := sum_choose_succ_le (fun s => (z.2 s).length) Finset.univ
  have hs := runGen_sum_length_le (symbolic F (discreteSig S) ι) (fun _ => id) hq tbl z hz
  have hcast : (∑ s, (((z.2 s).length + 1).choose 2 : ℝ≥0∞)) ≤
      (((∑ s, (tbl s).length) + q + 1).choose 2 : ℝ≥0∞) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hc.trans (Nat.choose_le_choose 2 (Nat.add_le_add_right hs 1))
  gcongr

/-- Every measurable event on the hidden point and full run output satisfies the master
bound in both directions. -/
theorem prEvent_runGen_symbolic_le_add_of_support [Field F] [DecidableEq F] [DecidableEq ι]
    [Fintype S] [DecidableEq S] {α : Type} {σ : Sig S}
    [MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F)))]
    (xs : ProbComp (ι → F)) {D : S → ℕ} {ε : S → ℝ≥0∞} {B : ℝ≥0∞}
    (hD : σ.DegreeClosed D)
    (hε : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε s)
    (oa : OracleComp (genSpec F σ) α)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE D tbl)
    (hB : ∀ z ∈ support (runGen (symbolic F σ ι) (fun _ => id) oa tbl),
      ∑ s, (((z.2 s).length + 1).choose 2 : ℝ≥0∞) * ε s ≤ B)
    (E : Set ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F))))
    (hE : MeasurableSet E) :
    (Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
          (fun _ p => MvPolynomial.eval x p) oa tbl)}[
          (x, z) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
          (fun _ => id) oa tbl)}[(x, z) ∈ E] +
      B) ∧
    (Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
          (fun _ => id) oa tbl)}[(x, z) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
          (fun _ p => MvPolynomial.eval x p) oa tbl)}[
          (x, z) ∈ E] +
      B) := by
  let left : ProbComp ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F))) := do
    let x ← xs
    let z ← runGen (symbolic F σ ι) (fun _ p => MvPolynomial.eval x p) oa tbl
    pure (x, z)
  let right : ProbComp ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F))) := do
    let x ← xs
    let z ← runGen (symbolic F σ ι) (fun _ => id) oa tbl
    pure (x, z)
  have h : measureETVDist left right ≤ _ :=
    measureETVDist_runGen_symbolic_le_of_support xs hD hε oa tbl hd hB
  have hl := (prEvent_le_prEvent_add_measureETVDist left right (· ∈ E) hE.mem).trans
    (add_le_add le_rfl h)
  rw [measureETVDist_comm] at h
  have hr := (prEvent_le_prEvent_add_measureETVDist right left (· ∈ E) hE.mem).trans
    (add_le_add le_rfl h)
  simpa only [left, right, map_bind, map_pure, bind_pure_comp, Functor.map_map,
    Function.comp_def] using And.intro hl hr

/-- Every measurable event on the hidden point and full run output satisfies the master
bound in both directions. -/
theorem prEvent_runGen_symbolic_le_add_of_target [Field F] [DecidableEq F] [DecidableEq ι]
    [Fintype S] [DecidableEq S] {α : Type} {σ : Sig S}
    [MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F)))]
    (xs : ProbComp (ι → F)) {D : S → ℕ} {ε : S → ℝ≥0∞} {n : S → ℕ}
    (hD : σ.DegreeClosed D)
    (hε : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε s)
    (oa : OracleComp (genSpec F σ) α)
    (hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s))
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE D tbl)
    (E : Set ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F))))
    (hE : MeasurableSet E) :
    (Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
          (fun _ p => MvPolynomial.eval x p) oa tbl)}[
          (x, z) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
          (fun _ => id) oa tbl)}[(x, z) ∈ E] +
      (∑ s, (((tbl s).length + n s + 1).choose 2 : ℝ≥0∞) * ε s)) ∧
    (Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
          (fun _ => id) oa tbl)}[(x, z) ∈ E] ≤
      Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
          (fun _ p => MvPolynomial.eval x p) oa tbl)}[
          (x, z) ∈ E] +
      (∑ s, (((tbl s).length + n s + 1).choose 2 : ℝ≥0∞) * ε s)) := by
  apply prEvent_runGen_symbolic_le_add_of_support xs hD hε oa tbl hd _ E hE
  intro z hz
  apply Finset.sum_le_sum
  intro s _
  have hs := runGen_length_le_of_target (symbolic F σ ι) (fun _ => id) s (hn s) tbl z hz
  gcongr

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
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE (fun _ => d) tbl)
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

/-! ## Computational master theorem -/

/-- **T8.** If success forces a nonzero bounded-degree output polynomial to vanish, the
hidden-point success probability is at most the collision bound plus its root bound. -/
theorem prEvent_runGen_symbolic_le_add_of_polynomial_of_support
    [Field F] [DecidableEq F] [DecidableEq ι]
    [Fintype S] [DecidableEq S] {α : Type} {σ : Sig S}
    (xs : ProbComp (ι → F)) {D : S → ℕ} {ε : S → ℝ≥0∞} {B ε' : ℝ≥0∞}
    (hD : σ.DegreeClosed D)
    (hε : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε s)
    (oa : OracleComp (genSpec F σ) α)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE D tbl)
    (hB : ∀ z ∈ support (runGen (symbolic F σ ι) (fun _ => id) oa tbl),
      ∑ s, (((z.2 s).length + 1).choose 2 : ℝ≥0∞) * ε s ≤ B)
    (W : α × Tbl (fun _ : S => MvPolynomial ι F) → MvPolynomial ι F) (k : ℕ)
    (hW : ∀ z ∈ support (runGen (symbolic F σ ι) (fun _ => id) oa tbl),
      (W z).totalDegree ≤ k)
    (E : (ι → F) → (α × Tbl (fun _ : S => MvPolynomial ι F)) → Prop)
    (hE : ∀ x z, z ∈ support (runGen (symbolic F σ ι) (fun _ => id) oa tbl) →
      E x z → W z ≠ 0 ∧ MvPolynomial.eval x (W z) = 0)
    (hroot : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ k →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε') :
    Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
      (fun _ p => MvPolynomial.eval x p) oa tbl)}[E x z] ≤ B + ε' := by
  classical
  let : MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F))) := ⊤
  have hm := (prEvent_runGen_symbolic_le_add_of_support xs hD hε oa tbl hd hB
    {w | E w.1 w.2} MeasurableSet.of_discrete).1
  have hs : Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
      (fun _ => id) oa tbl)}[E x z] ≤ ε' := by
    rw [prEvent_bind_map_swap]
    simpa only [map_bind, Functor.map_map, id_eq] using
      prEvent_bind_le_of_forall_le_of_support
        (runGen (symbolic F σ ι) (fun _ => id) oa tbl)
        (fun z => (fun x => E x z) <$> xs) id (fun z hz => by
          simp only [Functor.map_map, id_eq]
          by_cases hw : W z = 0
          · rw [prEvent_eq_zero_of_forall_not xs _ (fun x hx => (hE x z hz hx).1 hw)]
            exact zero_le
          · exact (prEvent_mono xs _ _ (fun x hx => (hE x z hz hx).2)).trans
              (hroot (W z) hw (hW z hz)))
  exact hm.trans ((add_le_add hs le_rfl).trans_eq (add_comm _ _))

/-- **T8 with per-sort budgets.** The collision sum uses the budget and degree of each sort;
the output polynomial contributes one further root-probability bound. -/
theorem prEvent_runGen_symbolic_le_add_of_polynomial [Field F] [DecidableEq F] [DecidableEq ι]
    [Fintype S] [DecidableEq S] {α : Type} {σ : Sig S}
    (xs : ProbComp (ι → F)) {D : S → ℕ} {ε : S → ℝ≥0∞} {ε' : ℝ≥0∞} {n : S → ℕ}
    (hD : σ.DegreeClosed D)
    (hε : ∀ s (f : MvPolynomial ι F), f ≠ 0 → f.totalDegree ≤ D s →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε s)
    (oa : OracleComp (genSpec F σ) α)
    (hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s))
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE D tbl)
    (W : α × Tbl (fun _ : S => MvPolynomial ι F) → MvPolynomial ι F) (k : ℕ)
    (hW : ∀ z ∈ support (runGen (symbolic F σ ι) (fun _ => id) oa tbl),
      (W z).totalDegree ≤ k)
    (E : (ι → F) → (α × Tbl (fun _ : S => MvPolynomial ι F)) → Prop)
    (hE : ∀ x z, z ∈ support (runGen (symbolic F σ ι) (fun _ => id) oa tbl) →
      E x z → W z ≠ 0 ∧ MvPolynomial.eval x (W z) = 0)
    (hroot : ∀ f : MvPolynomial ι F, f ≠ 0 → f.totalDegree ≤ k →
      Pr{let x ← xs}[MvPolynomial.eval x f = 0] ≤ ε') :
    Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
      (fun _ p => MvPolynomial.eval x p) oa tbl)}[E x z] ≤
      (∑ s, (((tbl s).length + n s + 1).choose 2 : ℝ≥0∞) * ε s) + ε' := by
  apply prEvent_runGen_symbolic_le_add_of_polynomial_of_support xs hD hε oa tbl hd _
    W k hW E hE hroot
  intro z hz
  apply Finset.sum_le_sum
  intro s _
  have hs := runGen_length_le_of_target (symbolic F σ ι) (fun _ => id) s (hn s) tbl z hz
  gcongr

/-- Uniform hidden points over a finite field give the Schwartz–Zippel specialization
`choose (initial size + operation budget + 1) 2 * (d / card F)` of the joint master bound. -/
theorem measureETVDist_runGen_symbolic_uniform_le [Field F] [DecidableEq F]
    [Fintype F] [Finite ι] [DecidableEq ι] [SampleableType (ι → F)]
    [Fintype S] [DecidableEq S] {α : Type}
    [MeasurableSpace ((ι → F) × (α × Tbl (fun _ : S => MvPolynomial ι F)))]
    {d q : ℕ} (oa : OracleComp (genSpec F (discreteSig S)) α)
    (hq : IsQueryBoundP oa (fun i => isGroupOp i = true) q)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE (fun _ => d) tbl) :
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
  exact prob_eval_zero_univ_le_div f hf hdeg

end GroupModel
