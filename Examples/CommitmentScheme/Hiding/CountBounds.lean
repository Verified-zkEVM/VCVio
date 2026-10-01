/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/

module
public import Examples.CommitmentScheme.Hiding.Defs
public import VCVio.ProgramLogic.Unary.WP.Qualitative
import VCVio.ProgramLogic.Unary.HandlerSpecs

/-!
# Count bounds for commitment-scheme hiding
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

variable {M S C : Type} [DecidableEq M] [DecidableEq S]

attribute [local instance] Fintype.ofFinite

/-! ## Support and counting invariants

Structural facts about reachable states of the counting handler; none needs any structure on
the commitment type `C`. Per-query facts are structural triples for `hidingImplCountAll`, proved
by core `vcgen` and read against the support with `triple_stateT_iff_forall_support`; facts about
whole runs lift a per-query invariant with `simulateQ_triple_preserves_invariant` or, for a
query-budgeted count, `simulateQ_triple_ranked`. -/

section HandlerInvariants

open OracleComp.ProgramLogic Std.WP

lemma hidingImplCountAll_run_totalBound_current {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    IsTotalQueryBound
      ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))
      (t + 1) := by
  exact (hidingOa_totalBound_current A s).simulateQ_run_of_step
    (fun ms st => hidingImplCountAll_step_totalBound ms st) (∅, fun _ => 0)

/-- Run-level projection: for any fixed `s`, the shared counted implementation
projects to the `hidingImpl₁ s` execution on `hidingOa`. -/
theorem hidingRun_countAll_proj_eq_impl₁ {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    (simulateQ hidingImplCountAll (hidingOa A s)).run' (∅, fun _ => 0) =
      (simulateQ (hidingImpl₁ s) (hidingOa A s)).run' (∅, 0) := by
  simpa [StateT.run'] using
    (OracleComp.run'_simulateQ_eq_of_query_map_eq
      hidingImplCountAll (hidingImpl₁ s) (fun st => (st.1, st.2 s))
      (fun ms st => by
        simpa [Prod.map] using hidingImplCountAll_proj_eq_hidingImpl₁
          (M := M) (S := S) (C := C) s ms st)
      (hidingOa A s) (∅, fun _ => 0))

/-- One-step growth bound for the shared counted hiding implementation:
the total count increases by at most one. -/
lemma sum_counts_step_le_succ_hidingImplCountAll [Fintype S] (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    (∑ s' : S, x.2.2 s') ≤ (∑ s' : S, st.2 s') + 1 := by
  refine (triple_stateT_iff_forall_support _ (· = st)
    (fun _ st' => ∑ s', st'.2 s' ≤ ∑ s', st.2 s' + 1) ⊥).1 ?_ st rfl _ _ hx
  vcgen [hidingImplCountAll] <;> simp_all [sum_update_succ_count]

lemma hiding_distinguish_totalBound_of_choose_count_support
    [Fintype S] [Inhabited S] [Finite M]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {x : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hx : x ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    ∀ cm : C, IsTotalQueryBound (A.distinguish x.1.2 cm) (t - ∑ s : S, x.2.2 s) := by
  have : Fintype M := Fintype.ofFinite M
  have hres :
      IsTotalQueryBound
        (((CMOracle M S C).query (x.1.1, default) : OracleComp (CMOracle M S C) _) >>= fun cm =>
          A.distinguish x.1.2 cm)
        ((t + 1) - (∑ s : S, x.2.2 s)) := by
    simpa [hidingOa] using
      (IsTotalQueryBound.residual_of_mem_support_run_simulateQ_le_cost
        (spec := CMOracle M S C)
        (oa := A.choose)
        (ob := fun a =>
          ((CMOracle M S C).query (a.1, default) : OracleComp (CMOracle M S C) _) >>= fun cm =>
            A.distinguish a.2 cm)
        (n := t + 1)
        (impl := hidingImplCountAll)
        (cost := fun st : QueryCache (CMOracle M S C) × (S → ℕ) => ∑ s : S, st.2 s)
        (hstep := fun t st y hy =>
          sum_counts_step_le_succ_hidingImplCountAll (M := M) (S := S) (C := C) t st y hy)
        (h := A.totalBound default)
        hx)
  rw [isTotalQueryBound_query_bind_iff] at hres
  intro cm
  have hcm :
      IsTotalQueryBound (A.distinguish x.1.2 cm)
        ((((t + 1) - ∑ s : S, x.2.2 s)) - 1) := by
    simpa using hres.2 cm
  have hbudget : ((((t + 1) - ∑ s : S, x.2.2 s)) - 1) = t - ∑ s : S, x.2.2 s := by
    omega
  simpa [hbudget] using hcm

/-- A counted query never decreases a salt counter: a lower bound on the counter at `s` is
preserved. -/
theorem hidingImplCountAll_triple_count_le (s : S) (c : ℕ) (ms : M × S) :
    ⦃ fun st => c ≤ st.2 s ⦄ hidingImplCountAll (M := M) (S := S) (C := C) ms
    ⦃ fun _ st' => c ≤ st'.2 s ⦄ := by
  vcgen [hidingImplCountAll]
  grind [Function.update_apply]

/-- A single counted query can only increase a fixed salt counter. -/
lemma count_mono_step_hidingImplCountAll (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    st.2 s ≤ x.2.2 s :=
  (triple_stateT_iff_forall_support _ _ _ _).1
    (hidingImplCountAll_triple_count_le s (st.2 s) ms) st le_rfl _ _ hx

/-- A single counted query changes any fixed salt counter by at most one. -/
lemma count_coord_le_succ_of_mem_support_step_hidingImplCountAll
    (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    st.2 s ≤ x.2.2 s ∧ x.2.2 s ≤ st.2 s + 1 := by
  refine (triple_stateT_iff_forall_support _ (· = st)
    (fun _ st' => st.2 s ≤ st'.2 s ∧ st'.2 s ≤ st.2 s + 1) ⊥).1 ?_ st rfl _ _ hx
  vcgen [hidingImplCountAll] <;> grind [Function.update_apply]

/-- A single counted query only changes the counter at its queried salt. -/
lemma count_coord_le_add_hit_of_mem_support_step_hidingImplCountAll
    (s : S) (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    x.2.2 s ≤ st.2 s + if ms.2 = s then 1 else 0 := by
  refine (triple_stateT_iff_forall_support _ (· = st)
    (fun _ st' => st'.2 s ≤ st.2 s + if ms.2 = s then 1 else 0) ⊥).1 ?_ st rfl _ _ hx
  vcgen [hidingImplCountAll] <;> grind [Function.update_apply]

/-- After the challenge step at salt `s`, removing the mandatory challenge hit leaves
at most the pre-challenge salt count. -/
lemma challenge_countPred_le_initialCount_of_mem_support_step_hidingImplCountAll
    (m : M) (s : S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    {x : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) (m, s)).run st)) :
    x.2.2 s - 1 ≤ st.2 s := by
  have hsucc :
      x.2.2 s ≤ st.2 s + 1 :=
    (count_coord_le_succ_of_mem_support_step_hidingImplCountAll
      (M := M) (S := S) (C := C) s (m, s) st x hx).2
  omega

/-- Any support point of a counted step caches the queried point with the returned value. -/
lemma self_mem_cache_of_mem_support_step_hidingImplCountAll (ms : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    x.2.1 ms = some x.1 := by
  refine (triple_stateT_iff_forall_support _ (· = st)
    (fun u st' => st'.1 ms = some u) ⊥).1 ?_ st rfl _ _ hx
  vcgen [hidingImplCountAll] <;> simp_all

/-- The counted hiding invariant: every cached salt has a positive counter. -/
def HidingCountInv (st : QueryCache (CMOracle M S C) × (S → ℕ)) : Prop :=
  ∀ ms : M × S, ∀ u : C, st.1 ms = some u → 1 ≤ st.2 ms.2

/-- A counted query preserves the hiding count invariant. -/
theorem hidingImplCountAll_triple_hidingCountInv (ms₀ : M × S) :
    ⦃ HidingCountInv ⦄ hidingImplCountAll (M := M) (S := S) (C := C) ms₀
    ⦃ fun _ => HidingCountInv ⦄ := by
  vcgen [hidingImplCountAll]
  rename_i st hInv _
  intro ms u hms
  by_cases hEq : ms = ms₀
  · subst hEq; simp
  · have h_old : 1 ≤ st.2 ms.2 :=
      hInv ms u (by simpa [QueryCache.cacheQuery, Function.update, hEq] using hms)
    grind [Function.update_apply]

/-- The counted implementation preserves the hiding count invariant. -/
lemma hidingCountInv_step_hidingImplCountAll (ms₀ : M × S)
    (st : QueryCache (CMOracle M S C) × (S → ℕ)) (hInv : HidingCountInv st)
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms₀).run st)) :
    HidingCountInv x.2 :=
  (triple_stateT_iff_forall_support _ _ _ _).1
    (hidingImplCountAll_triple_hidingCountInv ms₀) st hInv _ _ hx

/-- Support points of `simulateQ hidingImplCountAll` have coordinatewise monotone counts. -/
lemma count_mono_of_mem_support_run_hidingImplCountAll {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (z : α × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀))
    (s : S) :
    st₀.2 s ≤ z.2.2 s :=
  (triple_stateT_iff_forall_support _ _ _ _).1 (simulateQ_triple_preserves_invariant _ _
    (hidingImplCountAll_triple_count_le s (st₀.2 s)) oa) st₀ le_rfl _ _ hz

/-- Every cached salt has a positive counter along the support of the counted run. -/
lemma hidingCountInv_of_mem_support_run_hidingImplCountAll {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (hInv : HidingCountInv st₀)
    (z : α × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    HidingCountInv z.2 :=
  (triple_stateT_iff_forall_support _ _ _ _).1 (simulateQ_triple_preserves_invariant _ _
    hidingImplCountAll_triple_hidingCountInv oa) st₀ hInv _ _ hz

/-- On the support of the counted choose run, a zero salt-count means no cache entry
at that salt can already exist. -/
lemma cache_none_of_zero_count_of_mem_support_run_hidingChoose
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (m : M) (s : S)
    (hzero : qchoose.2.2 s = 0) :
    qchoose.2.1 (m, s) = none := by
  have hInv₀ : HidingCountInv ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0) := by
    intro ms u hms
    simp at hms
  have hInv :
      HidingCountInv qchoose.2 :=
    hidingCountInv_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C)
      (oa := A.choose)
      (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
      hInv₀
      (z := qchoose)
      hqchoose
  by_cases hcache : qchoose.2.1 (m, s) = none
  · exact hcache
  · cases hsome : qchoose.2.1 (m, s) with
    | none =>
        contradiction
    | some u =>
        have hpos : 1 ≤ qchoose.2.2 s :=
          hInv (m, s) u hsome
        omega

/-- For a fresh salt after the choose phase, the challenge step of
`hidingImplCountAll` is necessarily the cache-miss branch and sets that salt count to `1`. -/
abbrev HidingCountState (M : Type) (S : Type) (C : Type) :=
  QueryCache (CMOracle M S C) × (S → ℕ)

lemma fresh_step_state_of_mem_support_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    {qch : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqch : qch ∈ support
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2)) :
    qch.2 =
      (qchoose.2.1.cacheQuery (qchoose.1.1, s) qch.1,
        Function.update qchoose.2.2 s 1) := by
  have hnone : qchoose.2.1 (qchoose.1.1, s) = none :=
    cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose qchoose.1.1 s hzero
  refine (triple_stateT_iff_forall_support _ (· = qchoose.2) (fun u st => st =
    (qchoose.2.1.cacheQuery (qchoose.1.1, s) u, Function.update qchoose.2.2 s 1)) ⊥).1
    ?_ _ rfl _ _ hqch
  vcgen [hidingImplCountAll] <;> simp_all

/-- On the support of the counted hiding run, the total count is at most `n`
plus the initial total count. -/
lemma sum_counts_le_of_mem_support_run_hidingImplCountAll [Fintype S]
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    (∑ s' : S, z.2.2 s') ≤ n + ∑ s' : S, st₀.2 s' := by
  refine (triple_stateT_iff_forall_support _ _ _ ⊥).1 (simulateQ_triple_ranked hidingImplCountAll
    (fun k st => ∑ s', st.2 s' + k ≤ n + ∑ s', st₀.2 s') (fun ms k => ?_)
    (fun k st h => by omega) oa n hbound) st₀ (by omega) _ _ hz
  vcgen [hidingImplCountAll] <;> simp_all [sum_update_succ_count] <;> omega

lemma cache_le_of_mem_support_run_hidingImplCountAll
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : HidingCountState M S C}
    {z : α × HidingCountState M S C}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    st₀.1 ≤ z.2.1 :=
  (triple_stateT_iff_forall_support _ _ _ ⊥).1 (simulateQ_triple_preserves_invariant _
    (fun st : HidingCountState M S C => st₀.1 ≤ st.1)
    (fun _ => by vcgen [hidingImplCountAll]; grind [QueryCache.le_cacheQuery]) oa)
    st₀ le_rfl _ _ hz

lemma exists_new_salt_cacheEntry_of_count_gt_one
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    (m0 : M) (s : S)
    {cache₀ : QueryCache (CMOracle M S C)} {counts₀ : S → ℕ}
    (hcount : counts₀ s = 1)
    (hself : ∃ v : C, cache₀ (m0, s) = some v)
    (hunique : ∀ m : M, m ≠ m0 → cache₀ (m, s) = none)
    {z : α × HidingCountState M S C}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run (cache₀, counts₀)))
    (hgt : 1 < z.2.2 s) :
    ∃ m : M, ∃ v : C, m ≠ m0 ∧ z.2.1 (m, s) = some v := by
  have := (triple_stateT_iff_forall_support _ _ _ ⊥).1 (simulateQ_triple_preserves_invariant _
    (fun st : HidingCountState M S C =>
      (st.2 s = 1 ∧ (∃ v, st.1 (m0, s) = some v) ∧ ∀ m ≠ m0, st.1 (m, s) = none) ∨
        ∃ m v, m ≠ m0 ∧ st.1 (m, s) = some v) (fun ms => ?_) oa)
    _ (Or.inl ⟨hcount, hself, hunique⟩) _ _ hz
  · grind
  · vcgen [hidingImplCountAll]
    grind [Function.update_apply]

/-- Along the counted choose run, the total per-salt miss count is bounded by the
adversary query budget `t`. -/
lemma sum_counts_le_queryBound_of_mem_support_run_hidingChoose [Inhabited C]
    [Fintype S] [Inhabited S]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0))) :
    (∑ s : S, qchoose.2.2 s) ≤ t := by
  simpa using
    (sum_counts_le_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C)
      (oa := A.choose)
      (hbound := hiding_choose_totalBound (M := M) (S := S) (C := C) A)
      (st₀ := ((∅ : QueryCache (CMOracle M S C)), fun _ : S => 0))
      (z := qchoose)
      hqchoose)

/-- Every support point of `simulateQ hidingImplCountAll` is dominated by some
`countingOracle.simulate` support point: the total count across all salts is
bounded by the initial counts plus the counting oracle's total query cost. -/
lemma exists_counting_support_of_mem_support_run_hidingImplCountAll
    [Fintype M] [Fintype S]
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    ∃ qc : QueryCount (M × S),
      (z.1, qc) ∈ support (countingOracle.simulate oa 0) ∧
      (∑ s : S, z.2.2 s) ≤ (∑ s : S, st₀.2 s) + ∑ ms : M × S, qc ms := by
  classical
  induction oa using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      refine ⟨0, ?_, ?_⟩
      · simpa using
          (countingOracle.mem_support_simulate_pure_iff
            (x := x) (qc := (0 : QueryCount (M × S))) (z := (x, 0))).2 rfl
      · simp
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      rcases ih qu.1 (st₀ := qu.2) (z := z) hz' with ⟨qcRest, hqcRest, hsumRest⟩
      have hstep :
          (∑ s : S, qu.2.2 s) ≤ (∑ s : S, st₀.2 s) + 1 :=
        sum_counts_step_le_succ_hidingImplCountAll
          (M := M) (S := S) (C := C) t st₀ qu hqu
      let qc : QueryCount (M × S) := Function.update qcRest t (qcRest t + 1)
      have hpred : Function.update qc t (qc t - 1) = qcRest := by
        funext j
        by_cases hj : j = t
        · subst hj
          simp [qc]
        · simp [qc, Function.update, hj]
      have hqc :
          (z.1, qc) ∈ support
            (countingOracle.simulate
              (((CMOracle M S C).query t : OracleComp (CMOracle M S C) _) >>=
                mx) 0) := by
        rw [countingOracle.mem_support_simulate_queryBind_iff]
        refine ⟨by simp [qc], qu.1, ?_⟩
        simpa [hpred] using hqcRest
      have hqcsum : (∑ ms : M × S, qc ms) = (∑ ms : M × S, qcRest ms) + 1 := by
        simpa [qc] using sum_update_succ_count (counts := qcRest) t
      refine ⟨qc, hqc, ?_⟩
      omega

/-- Per-coordinate variant of `exists_counting_support_of_mem_support_run_hidingImplCountAll`:
for each salt `t`, the per-salt count `z.2.2 t` is bounded by the initial count
plus the counting oracle's per-index query count at `t`. -/
lemma exists_counting_support_of_mem_support_run_hidingImplCountAll_coord [Fintype M]
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) :
    ∃ qc : QueryCount (M × S),
      (z.1, qc) ∈ support (countingOracle.simulate oa 0) ∧
      ∀ s : S, z.2.2 s ≤ st₀.2 s + ∑ m : M, qc (m, s) := by
  classical
  induction oa using OracleComp.inductionOn generalizing st₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      refine ⟨0, ?_, ?_⟩
      · simpa using
          (countingOracle.mem_support_simulate_pure_iff
            (x := x) (qc := (0 : QueryCount (M × S))) (z := (x, 0))).2 rfl
      · intro s
        simp
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨qu, hqu, hz'⟩ := hz
      rcases ih qu.1 (st₀ := qu.2) (z := z) hz' with ⟨qcRest, hqcRest, hcoordRest⟩
      let qc : QueryCount (M × S) := Function.update qcRest t (qcRest t + 1)
      have hpred : Function.update qc t (qc t - 1) = qcRest := by
        funext j
        by_cases hj : j = t
        · subst hj
          simp [qc]
        · simp [qc, Function.update, hj]
      have hqc :
          (z.1, qc) ∈ support
            (countingOracle.simulate
              (((CMOracle M S C).query t : OracleComp (CMOracle M S C) _) >>=
                mx) 0) := by
        rw [countingOracle.mem_support_simulate_queryBind_iff]
        refine ⟨by simp [qc], qu.1, ?_⟩
        simpa [hpred] using hqcRest
      refine ⟨qc, hqc, ?_⟩
      intro s
      have hstep :
          qu.2.2 s ≤ st₀.2 s + if t.2 = s then 1 else 0 :=
        count_coord_le_add_hit_of_mem_support_step_hidingImplCountAll
          (M := M) (S := S) (C := C) s t st₀ qu hqu
      have hrest :
          z.2.2 s ≤ qu.2.2 s + ∑ m : M, qcRest (m, s) :=
        hcoordRest s
      by_cases hs : t.2 = s
      · subst hs
        have hcoord :
            (fun m : M => qc (m, t.2)) =
              Function.update (fun m : M => qcRest (m, t.2)) t.1 (qcRest t + 1) := by
          funext m
          by_cases hm : m = t.1
          · subst hm
            simp [qc]
          · have hne : (m, t.2) ≠ t := by
              intro hEq
              exact hm (by simpa using congrArg Prod.fst hEq)
            simp [qc, Function.update_of_ne hne, hm]
        have hsum :
            (∑ m : M, qc (m, t.2)) = (∑ m : M, qcRest (m, t.2)) + 1 := by
          rw [hcoord]
          simpa using
            sum_update_succ_count (counts := fun m : M => qcRest (m, t.2)) t.1
        have hstep' :
            qu.2.2 t.2 + ∑ m : M, qcRest (m, t.2) ≤
              st₀.2 t.2 + ∑ m : M, qc (m, t.2) := by
          rw [hsum]
          have := add_le_add_right hstep (∑ m : M, qcRest (m, t.2))
          simpa [add_assoc, add_left_comm, add_comm] using this
        exact le_trans hrest hstep'
      · have hsum :
            (∑ m : M, qc (m, s)) = ∑ m : M, qcRest (m, s) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          have hne : (m, s) ≠ t := by
            intro hEq
            exact hs (by simpa using congrArg Prod.snd hEq.symm)
          rw [show qc (m, s) = qcRest (m, s) by
            simp [qc, Function.update_of_ne hne]]
        have hstep' :
            qu.2.2 s + ∑ m : M, qcRest (m, s) ≤
              st₀.2 s + ∑ m : M, qc (m, s) := by
          rw [hsum]
          have := add_le_add_right hstep (∑ m : M, qcRest (m, s))
          simpa [hs, add_assoc, add_left_comm, add_comm] using this
        exact le_trans hrest hstep'

/-- On the support of the counted hiding run, the challenge salt count is positive. -/
theorem challenge_count_pos_of_mem_support_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    1 ≤ z.2.2 s := by
  refine (triple_stateT_iff_forall_support _ HidingCountInv (fun _ st => 1 ≤ st.2 s) ⊥).1 ?_ _
    (fun _ _ h => by simp at h) _ _ hz
  simp only [hidingOa, simulateQ_bind, simulateQ_query]
  vcgen [hidingImplCountAll, simulateQ_triple_preserves_invariant _ _
      hidingImplCountAll_triple_hidingCountInv A.choose,
    fun aux cm => simulateQ_triple_preserves_invariant _ _
      (hidingImplCountAll_triple_count_le s 1) (A.distinguish aux cm)]
  · rename_i hInv _ h; exact hInv _ _ h
  · simp

/-- On support of the counted hiding run, the bad-event indicator at the challenge salt
is bounded by the excess of that salt count over the mandatory challenge hit. -/
lemma bad_indicator_le_count_pred_of_mem_support_run_hidingImplCountAll
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    (if 2 ≤ z.2.2 s then (1 : ℝ≥0∞) else 0) ≤ z.2.2 s - 1 := by
  have hpos : 1 ≤ z.2.2 s :=
    challenge_count_pos_of_mem_support_hidingImplCountAll
      (M := M) (S := S) (C := C) A s hz
  by_cases hbad : 2 ≤ z.2.2 s
  · have hcount : (1 : ℕ) ≤ z.2.2 s - 1 := by omega
    simp only [ge_iff_le, hbad, ↓reduceIte]
    exact_mod_cast hcount
  · simp [hbad]

/-- On support of the counted hiding run, bad at salt `s` can only happen if the
choose phase already queried salt `s`, or if the distinguish phase later
increased the salt-`s` counter after the challenge step. -/
lemma bad_indicator_le_chooseHitIndicator_add_distinguishIncrementIndicator
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (_hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    {qch : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqch : qch ∈ support
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2))
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)) :
    propInd (2 ≤ z.2.2 s) ≤
      propInd (0 < qchoose.2.2 s) +
        propInd (qch.2.2 s < z.2.2 s) := by
  by_cases hbad : 2 ≤ z.2.2 s
  · by_cases hchoose : 0 < qchoose.2.2 s
    · simp [propInd, hbad, hchoose]
    · have hqzero : qchoose.2.2 s = 0 := Nat.eq_zero_of_not_pos hchoose
      have hmono :
          qch.2.2 s ≤ z.2.2 s :=
        count_mono_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C)
          (oa := A.distinguish qchoose.1.2 qch.1)
          (st₀ := qch.2) (z := z) hz s
      have hstep :
          qch.2.2 s ≤ qchoose.2.2 s + 1 :=
        (count_coord_le_succ_of_mem_support_step_hidingImplCountAll
          (M := M) (S := S) (C := C) s (qchoose.1.1, s) qchoose.2 qch hqch).2
      have hinc : qch.2.2 s < z.2.2 s := by
        by_contra hnot
        have hzle : z.2.2 s ≤ qch.2.2 s := Nat.le_of_not_gt hnot
        have hEq : z.2.2 s = qch.2.2 s := le_antisymm hzle hmono
        have hzle1 : z.2.2 s ≤ 1 := by
          rw [hEq]
          simpa [hqzero] using hstep
        omega
      simp [propInd, hbad, hchoose, hinc]
  · simp [propInd, hbad]

/-- Strengthened version of
`bad_indicator_le_chooseHitIndicator_add_distinguishIncrementIndicator`:
the distinguish-increment term is only charged on salts that were fresh after
the choose phase. -/
lemma bad_indicator_le_chooseHitIndicator_add_freshDistinguishIncrementIndicator
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (_hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    {qch : C × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqch : qch ∈ support
      ((hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2))
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support
      ((simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2)) :
    propInd (2 ≤ z.2.2 s) ≤
      propInd (0 < qchoose.2.2 s) +
        propInd
          (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s) := by
  by_cases hbad : 2 ≤ z.2.2 s
  · by_cases hchoose : 0 < qchoose.2.2 s
    · simp [propInd, hbad, hchoose]
    · have hqzero : qchoose.2.2 s = 0 := Nat.eq_zero_of_not_pos hchoose
      have hmono :
          qch.2.2 s ≤ z.2.2 s :=
        count_mono_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C)
          (oa := A.distinguish qchoose.1.2 qch.1)
          (st₀ := qch.2) (z := z) hz s
      have hstep :
          qch.2.2 s ≤ qchoose.2.2 s + 1 :=
        (count_coord_le_succ_of_mem_support_step_hidingImplCountAll
          (M := M) (S := S) (C := C) s (qchoose.1.1, s) qchoose.2 qch hqch).2
      have hinc : qch.2.2 s < z.2.2 s := by
        by_contra hnot
        have hzle : z.2.2 s ≤ qch.2.2 s := Nat.le_of_not_gt hnot
        have hEq : z.2.2 s = qch.2.2 s := le_antisymm hzle hmono
        have hzle1 : z.2.2 s ≤ 1 := by
          rw [hEq]
          simpa [hqzero] using hstep
        omega
      simp [propInd, hbad, hqzero, hinc]
  · simp [propInd, hbad]

/-- On support of the counted hiding run, the challenge-salt excess count is bounded
by the adversary's total query budget. -/
lemma count_pred_le_queryBound_of_mem_support_run_hidingImplCountAll
    [Finite S]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    z.2.2 s - 1 ≤ t := by
  have : Fintype S := Fintype.ofFinite S
  have hsum :
      (∑ s' : S, z.2.2 s') ≤ t + 1 := by
      simpa using
        (sum_counts_le_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C)
          (oa := hidingOa A s)
          (hbound := hidingOa_totalBound_current (M := M) (S := S) (C := C) A s)
          (st₀ := (∅, fun _ => 0)) (z := z) hz)
  have hs_le : z.2.2 s ≤ ∑ s' : S, z.2.2 s' := by
    classical
    simpa using Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  omega

/- Combined pointwise bound used when converting the bad event to an indicator
expectation over counted support points. -/
lemma bad_indicator_le_queryBound_of_mem_support_run_hidingImplCountAll
    [Finite S]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S)
    {z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))) :
    (if 2 ≤ z.2.2 s then (1 : ℝ≥0∞) else 0) ≤ t := by
  have : Fintype S := Fintype.ofFinite S
  exact le_trans
    (bad_indicator_le_count_pred_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C) A s hz)
    (by
      exact_mod_cast
        (count_pred_le_queryBound_of_mem_support_run_hidingImplCountAll
          (M := M) (S := S) (C := C) A s hz))

end HandlerInvariants

/-! ## Probability bounds

The bounds below evaluate probabilities and weakest preconditions over `CMOracle M S C`, whose
uniform interpretation needs a finite inhabited commitment type with measurable singletons. -/

variable [Finite C] [Inhabited C]

/-- Probability bridge for bad events:
`Pr[bad]` under `hidingImpl₁ s` is equal to the corresponding event on the
shared counted run, projected at `s`. -/
theorem prEvent_hidingBad_eq_countAll {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    Pr{let z ← (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0)}[hidingBad z.2] =
    Pr{let z ← (
      (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0))}[2 ≤ z.2.2 s] := by
  have hrun :
      Prod.map id (fun st : QueryCache (CMOracle M S C) × (S → ℕ) => (st.1, st.2 s)) <$>
          (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0) =
        (simulateQ (hidingImpl₁ s) (hidingOa A s)).run (∅, 0) := by
    simpa using
      (OracleComp.map_run_simulateQ_eq_of_query_map_eq
        hidingImplCountAll (hidingImpl₁ s) (fun st => (st.1, st.2 s))
        (fun ms st => by
          simpa [Prod.map] using hidingImplCountAll_proj_eq_hidingImpl₁
            (M := M) (S := S) (C := C) s ms st)
        (hidingOa A s) (∅, fun _ => 0))
  rw [← hrun]
  rw [prEvent_map]
  rfl

lemma wp_fresh_challenge_branch_eq
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S)
    (hzero : qchoose.2.2 s = 0)
    (F : C × (QueryCache (CMOracle M S C) × (S → ℕ)) → ℝ≥0∞) :
    wp⟦(hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2⟧
      F
    =
    wp⟦((CMOracle M S C).query (qchoose.1.1, s) :
        OracleComp (CMOracle M S C) C)⟧
      (fun cm =>
        F (cm, (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
          Function.update qchoose.2.2 s 1))) := by
  have hnone : qchoose.2.1 (qchoose.1.1, s) = none :=
    cache_none_of_zero_count_of_mem_support_run_hidingChoose
      (M := M) (S := S) (C := C) A hqchoose qchoose.1.1 s hzero
  simp only [hidingImplCountAll, bind_pure_comp, StateT.run_bind, StateT.run_get,
    pure_bind, hnone, hzero, zero_add, StateT.run_monadLift, StateT.run_map,
    StateT.run_set, map_pure, Functor.map_map]
  rw [ExpectationWP.wp_map]

lemma wp_freshDistinguishIncrement_eq
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t)
    {qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hqchoose : qchoose ∈ support ((simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)))
    (s : S) :
    wp⟦(hidingImplCountAll (M := M) (S := S) (C := C) (qchoose.1.1, s)).run qchoose.2⟧
      (fun qch : C × HidingCountState M S C =>
        wp⟦(simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2⟧
          (fun z : Bool × HidingCountState M S C =>
            propInd
              (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) =
      propInd (qchoose.2.2 s = 0) *
        wp⟦((CMOracle M S C).query (qchoose.1.1, s) :
            OracleComp (CMOracle M S C) C)⟧
          (fun cm =>
            wp⟦(simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 cm)).run
                (qchoose.2.1.cacheQuery (qchoose.1.1, s) cm,
                  Function.update qchoose.2.2 s 1)⟧
              (fun z : Bool × HidingCountState M S C =>
                propInd (1 < z.2.2 s))) := by
  by_cases hzero : qchoose.2.2 s = 0
  · rw [wp_fresh_challenge_branch_eq
        (M := M) (S := S) (C := C) A hqchoose s hzero]
    simp [hzero]
  · have hpost :
        (fun qch : C × HidingCountState M S C =>
          wp⟦(simulateQ hidingImplCountAll (A.distinguish qchoose.1.2 qch.1)).run qch.2⟧
            (fun z : Bool × HidingCountState M S C =>
              propInd
                (qchoose.2.2 s = 0 ∧ qch.2.2 s < z.2.2 s))) = fun _ => 0 := by
      funext qch
      simp only [hzero, false_and, propInd_false]
      exact ExpectationWP.wp_const_of_oracle _ 0
    rw [hpost]
    simp [hzero]

lemma wp_choose_sumCounts_le_queryBound [Fintype S] [Inhabited S]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) :
    wp⟦(simulateQ hidingImplCountAll A.choose).run (∅, fun _ => 0)⟧
      (fun qchoose : (M × AUX) × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
        (∑ s : S, qchoose.2.2 s : ℝ≥0∞)) ≤ t := by
  apply OracleComp.ProgramLogic.wp_le_const_of_support
  intro qchoose hqchoose
  exact_mod_cast sum_counts_le_queryBound_of_mem_support_run_hidingChoose
    (M := M) (S := S) (C := C) A hqchoose

/-- Fixed-salt bridge from the counted bad event to the expected excess count. -/
lemma prEvent_countAll_bad_le_wp_countPred
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    Pr{let z ← (simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)}[2 ≤ z.2.2 s] ≤
    wp⟦(simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)⟧
      (fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞)) := by
  rw [OracleComp.ProgramLogic.prEvent_eq_wp_propInd]
  refine wp_mono_of_support _ fun z hz => ?_
  simp only [propInd_eq_ite]
  exact bad_indicator_le_count_pred_of_mem_support_run_hidingImplCountAll
    (M := M) (S := S) (C := C) A s hz

/- Fixed-salt expectation bound for the counted excess at the challenge salt. -/
lemma wp_countPred_le_queryBound_of_run_hidingImplCountAll
    [Finite S]
    {AUX : Type} {t : ℕ}
    (A : HidingAdversary M S C AUX t) (s : S) :
    wp⟦(simulateQ hidingImplCountAll (hidingOa A s)).run (∅, fun _ => 0)⟧
      (fun z : Bool × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
        (z.2.2 s - 1 : ℝ≥0∞)) ≤ t := by
  apply OracleComp.ProgramLogic.wp_le_const_of_support
  intro z hz
  exact_mod_cast count_pred_le_queryBound_of_mem_support_run_hidingImplCountAll
    (M := M) (S := S) (C := C) A s hz

/-- For a fixed computation under the shared counted implementation, the sum of
expected per-salt count increments is bounded by the total query bound. -/
lemma sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll [Fintype S]
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ)) :
    (∑ s : S,
      wp⟦(simulateQ hidingImplCountAll oa).run st₀⟧
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          (z.2.2 s - st₀.2 s : ℝ≥0∞))) ≤ n := by
  rw [← OracleComp.ProgramLogic.wp_finsetSum]
  apply OracleComp.ProgramLogic.wp_le_const_of_support
  intro z hz
  have hmono : ∀ s, st₀.2 s ≤ z.2.2 s :=
    count_mono_of_mem_support_run_hidingImplCountAll
      (M := M) (S := S) (C := C) oa st₀ z hz
  have htotal := sum_counts_le_of_mem_support_run_hidingImplCountAll
    (M := M) (S := S) (C := C) hbound hz
  have hdiff : (∑ s : S, (z.2.2 s - st₀.2 s)) ≤ n := by
    rw [Finset.sum_tsub_distrib _ (fun s _ => hmono s)]
    omega
  exact_mod_cast hdiff

/-- For a fixed computation under the shared counted implementation, the sum of
expected indicators of whether each salt counter ever increases is bounded by the
total query bound. -/
lemma sum_wp_countIncrementIndicators_le_queryBound_of_run_hidingImplCountAll
    [Fintype S]
    {α : Type} {oa : OracleComp (CMOracle M S C) α} {n : ℕ}
    (hbound : IsTotalQueryBound oa n)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ)) :
    (∑ s : S,
      wp⟦(simulateQ hidingImplCountAll oa).run st₀⟧
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) =>
          propInd (st₀.2 s < z.2.2 s))) ≤ n := by
  refine le_trans ?_
    (sum_wp_countIncrements_le_queryBound_of_run_hidingImplCountAll hbound st₀)
  gcongr with s _ z hz
  by_cases hinc : st₀.2 s < z.2.2 s
  · have hdiff : 1 ≤ z.2.2 s - st₀.2 s := by omega
    simpa only [propInd, hinc, ↓reduceIte,
      ENNReal.natCast_sub] using
      (show (1 : ℝ≥0∞) ≤ (z.2.2 s - st₀.2 s : ℕ) from by exact_mod_cast hdiff)
  · simp [propInd, hinc]

/-- A selected final count decomposes into the initial selected count plus the
new increments made during the run. -/
lemma wp_countPred_le_initialPred_add_wp_countIncrement
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (s : S) :
    wp⟦(simulateQ hidingImplCountAll oa).run st₀⟧
      (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞)) ≤
    (st₀.2 s - 1 : ℝ≥0∞) +
      wp⟦(simulateQ hidingImplCountAll oa).run st₀⟧
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
  apply OracleComp.ProgramLogic.wp_le_const_add_of_support
  intro z hz
  have hmono := count_mono_of_mem_support_run_hidingImplCountAll
    (M := M) (S := S) (C := C) oa st₀ z hz s
  exact_mod_cast (show z.2.2 s - 1 ≤ (st₀.2 s - 1) + (z.2.2 s - st₀.2 s) by omega)

lemma sum_wp_countPred_le_sum_initialPred_add_sum_wp_countIncrements [Fintype S]
    {α : Type}
    (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ)) :
    (∑ s : S,
      wp⟦(simulateQ hidingImplCountAll oa).run st₀⟧
        (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - 1 : ℝ≥0∞))) ≤
    (∑ s : S, (st₀.2 s - 1 : ℝ≥0∞)) +
      ∑ s : S,
        wp⟦(simulateQ hidingImplCountAll oa).run st₀⟧
          (fun z : α × (QueryCache (CMOracle M S C) × (S → ℕ)) => (z.2.2 s - st₀.2 s : ℝ≥0∞)) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun s _ =>
    wp_countPred_le_initialPred_add_wp_countIncrement oa st₀ s

/-- The simulated hiding game, parametrized by salt `s`.

The adversary runs `hidingOa A s` (which includes the challenge query `(m, s)`)
through `hidingImplSim`, which redirects ALL salt-`s` cache misses to
`(default, default)`. This makes the challenge commitment independent of `m`:
the challenge `query (m, s)` is redirected → returns fresh uniform, independent
of `m`. The salt counter is discarded by `run'`.

Using `hidingImplSim` allows direct application of the distributional
identical-until-bad lemma (`measureETVDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq`) to bound
the distance between `hidingReal` and `hidingSim`. -/
def hidingSim [Inhabited M] [Inhabited S]
    {AUX : Type} {t : ℕ} (A : HidingAdversary M S C AUX t) (s : S) :
    OracleComp (CMOracle M S C) Bool :=
  (simulateQ (hidingImplSim s) (hidingOa A s)).run' (∅, 0)

abbrev HidingAvgSpec (M : Type) (S : Type) (C : Type) :=
  (Unit →ₒ S) + CMOracle M S C

/-- Uniform sampling of a salt in its chosen finite response space. -/
noncomputable instance unitArrowSpecIsUniformMeasureSpec (S : Type) [Fintype S] [Inhabited S] :
    OracleSpec.IsUniformMeasureSpec (Unit →ₒ S) :=
  OracleSpec.IsUniformMeasureSpec.ofFiniteNonempty _

abbrev hidingAvgLeftImpl :
    QueryImpl (Unit →ₒ S)
      (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C))) :=
  (QueryImpl.ofLift (Unit →ₒ S) (OracleComp (HidingAvgSpec M S C))).liftTarget
    (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C)))

abbrev hidingAvgRightImpl :
    QueryImpl (CMOracle M S C)
      (StateT (HidingCountState M S C) (OracleComp (HidingAvgSpec M S C))) :=
  fun t =>
    StateT.mk fun st =>
      OracleComp.liftComp
        ((hidingImplCountAll (M := M) (S := S) (C := C) t).run st)
        (HidingAvgSpec M S C)
