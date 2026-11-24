/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.Rewinding.FinderBridge
public import VCVio.CryptoFoundations.Rewinding.QueriedPoints
public import VCVio.CryptoFoundations.Rewinding.ThresholdSemantics

/-!
# Recovering transcripts from a finder

A finder (`Rewinding.IsFinder`) sees only the verdicts of complete runs. To extract a witness, the
transcripts at the challenges of its output are needed as well. `Rewinding.recover` runs a finder
against the verdicts of frozen reruns, caching the output of every run it makes. On success, it
looks up the transcript at every point of the output in the cache, rerunning only on a miss, and
hands the transcripts to an extractor.

Against a fixed table of complete outputs, the recovered transcripts are the table's entries at the
output's points (`Rewinding.run_simulateQ_counted_recover`), so they are exactly the runs whose
verdicts the finder saw. Against frozen reruns, the eager representation
(`Rewinding.ResetPolicy.attempt_eagerTable`) carries this over
(`Rewinding.ResetPolicy.attempt_recover`). A sound finder queries every point it vouches for
(`Rewinding.IsFinder.mem_log_of_mem_support`), so there are no misses, and the finder's success
and cost bounds become an extractor's with no further complete runs
(`Rewinding.ResetPolicy.recover_bounds`).

## Main definitions

* `Rewinding.cachingImpl`: answer an acceptance query by a complete rerun, cache its output, and
  return its verdict.
* `Rewinding.lookupAll`: look up finitely many inputs in a cache, rerunning only on a miss.
* `Rewinding.recover`: find, recover the transcripts from the cache, extract.

## Main results

* `Rewinding.ResetPolicy.eagerTable_settled`: every table in the eager table's support is settled
  in one world.
* `Rewinding.ResetPolicy.eagerTable_fst_eq`: runs that share a first phase give one public value
  in every table, as a Σ-protocol's commitment.
* `Rewinding.run_simulateQ_counted_caching`: against a fixed table, the caching finder is the
  logged finder, its cache holding the table's entries at the logged vectors.
* `Rewinding.ResetPolicy.attempt_recover`: against frozen reruns, recovery is the logged finder
  against the verdicts of an eager table, followed by extraction from the same table.
* `Rewinding.ResetPolicy.recover_bounds`: the finder's affine success bound and its cost transfer
  to the extractor.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Rewinding

/-! ## Tables in the eager table's support -/

namespace ResetPolicy

variable {ι σ : Type} {spec : OracleSpec ι} {init : ProbComp σ}
  {impl : QueryImpl spec (StateT σ ProbComp)} (P : ResetPolicy init impl)

/-- Every table in the eager table's support is settled in one world: each complete rerun is a
pure lookup of its entry there. -/
theorem eagerTable_settled {Q α : Type} [Finite Q] (run : Q → OracleComp spec α) {F : Q → α}
    (hF : F ∈ support (P.eagerTable run)) :
    ∃ w, ∀ q, (P.runWorld run q).run w = pure (F q, w) := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  simp only [eagerTable, support_map, Set.mem_image] at hF
  obtain ⟨z, hz, rfl⟩ := hF
  refine ⟨z.2, fun q => ?_⟩
  simpa only [Equiv.symm_apply_apply] using
    (P.draw_support run (Fintype.equivFin Q).symm P.empty z hz).2 (Fintype.equivFin Q q)

/-- Runs that share a first phase `pre` and publish `pub` of its result give one public value in
every table of the eager table's support. For a Σ-protocol prover, the first phase is the
commitment, so every recovered transcript has the same commitment. -/
theorem eagerTable_fst_eq {Q S A B : Type} [Finite Q] (pre : OracleComp spec S) (pub : S → A)
    (post : S → Q → OracleComp spec B) {F : Q → A × B}
    (hF : F ∈ support (P.eagerTable fun q => pre >>= fun s => (pub s, ·) <$> post s q))
    (q q' : Q) : (F q).1 = (F q').1 := by
  obtain ⟨w, hw⟩ := P.eagerTable_settled _ hF
  have key : ∀ q, ∀ s ∈ support ((simulateQ P.answer pre).run (w, P.begin)), (F q).1 = pub s.1 := by
    intro q s hs
    obtain ⟨y, hy⟩ := support_nonempty ((simulateQ P.answer (post s.1 q)).run s.2)
    have hmem : ((pub s.1, y.1), y.2.1) ∈ support ((P.runWorld (fun q =>
        pre >>= fun s => (pub s, ·) <$> post s q) q).run w) := by
      simp only [runWorld, StateT.run_mk, simulateQ_bind, simulateQ_map, StateT.run_bind,
        StateT.run_map, support_map, support_bind, Set.mem_image, Set.mem_iUnion]
      exact ⟨((pub s.1, y.1), y.2), ⟨s, hs, y, hy, rfl⟩, rfl⟩
    rw [hw q, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact congrArg Prod.fst hmem.1.symm
  obtain ⟨s, hs⟩ := support_nonempty ((simulateQ P.answer pre).run (w, P.begin))
  rw [key q s hs, key q' s hs]

end ResetPolicy

/-- A continuation that adds at most `B` to the counter adds at most `B` to the expected
counter. -/
theorem expectedCalls_bind_le_add {β γ : Type} (mx : ProbComp (β × ℕ))
    (f : β × ℕ → ProbComp (γ × ℕ)) (B : ℕ)
    (hf : ∀ z ∈ support mx, ∀ y ∈ support (f z), y.2 ≤ z.2 + B) :
    expectedCalls (mx >>= f) ≤ expectedCalls mx + B := by
  let : MeasurableSpace (β × ℕ) := ⊤
  rw [expectedCalls_bind]
  calc
    (∫⁻ z, expectedCalls (f z) ∂𝒟[mx]) ≤ ∫⁻ z, ((z.2 : ℝ≥0∞) + B) ∂𝒟[mx] := by
      apply lintegral_mono_ae
      apply evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
      intro z hz
      rw [expectedCalls_eq_lintegral_counter]
      calc
        (∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> f z]) ≤
            ∫⁻ _n, ((z.2 : ℝ≥0∞) + B) ∂𝒟[Prod.snd <$> f z] := by
          apply lintegral_mono_ae
          apply evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
          intro n hn
          rw [support_map] at hn
          obtain ⟨y, hy, rfl⟩ := hn
          exact_mod_cast hf z hz y hy
        _ = ((z.2 : ℝ≥0∞) + B) * 𝒟[Prod.snd <$> f z] Set.univ := lintegral_const _
        _ ≤ (z.2 : ℝ≥0∞) + B := mul_le_of_le_one_right zero_le (evalDist_apply_univ_le_one _)
    _ = (∫⁻ z, (z.2 : ℝ≥0∞) ∂𝒟[mx]) + B * 𝒟[mx] Set.univ := by
      rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ expectedCalls mx + B := by
      rw [expectedCalls_eq_lintegral_counter, lintegral_evalDist_map_of_discrete]
      gcongr
      exact mul_le_of_le_one_right zero_le (evalDist_apply_univ_le_one mx)

section Cache

variable {Q α : Type}

/-- The finder against a fixed acceptance function, logging its queries from the empty log. -/
@[expose] def logRun {β : Type} (g : Q → Bool)
    (find : OracleComp (unifSpec + rerunSpec Q Bool) β) : ProbComp (β × (Set Q × ℕ)) :=
  (simulateQ (coins (S := Set Q × ℕ) + logCounted g) find).run (∅, 0)

/-- Group a logged run's output with its log, leaving its counter. -/
@[expose] def regroup {β S : Type} (z : β × (S × ℕ)) : (β × S) × ℕ := ((z.1, z.2.1), z.2.2)

open Classical in
/-- The cache holding a table's entries at the vectors of a log. -/
@[expose] noncomputable def cacheOf (F : Q → α) (L : Set Q) : Q → Option α :=
  fun q => if q ∈ L then some (F q) else none

/-- Recording a vector in the log caches the table's entry there. -/
theorem update_cacheOf [DecidableEq Q] (F : Q → α) (L : Set Q) (q : Q) :
    Function.update (cacheOf F L) q (some (F q)) = cacheOf F (insert q L) := by
  funext q'
  by_cases h : q' = q
  · subst h
    simp [cacheOf]
  · by_cases hL : q' ∈ L <;> simp [cacheOf, hL, h]

/-- The cache of the empty log is empty. -/
theorem cacheOf_empty (F : Q → α) : cacheOf F ∅ = fun _ => none := by
  funext q
  simp [cacheOf]

/-- Look up finitely many inputs in a cache, rerunning only on a miss. -/
@[expose] def lookupAll (cache : Q → Option α) :
    {m : ℕ} → (Fin m → Q) → OracleComp (unifSpec + rerunSpec Q α) (Fin m → α)
  | 0, _ => pure Fin.elim0
  | _ + 1, qs => do
      let a ← (cache (qs 0)).elim (liftM ((rerunSpec Q α).query (qs 0))) pure
      let ts ← lookupAll cache (Fin.tail qs)
      pure (Fin.cons a ts)

open Classical in
/-- The number of inputs missing from a log. -/
@[expose] noncomputable def missCount (L : Set Q) : {m : ℕ} → (Fin m → Q) → ℕ
  | 0, _ => 0
  | _ + 1, qs => (if qs 0 ∈ L then 0 else 1) + missCount L (Fin.tail qs)

/-- No input is missing from a log containing all of them. -/
theorem missCount_eq_zero (L : Set Q) {m : ℕ} (qs : Fin m → Q) (h : ∀ i, qs i ∈ L) :
    missCount L qs = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [missCount, h 0, ite_true, ih (Fin.tail qs) fun i => h i.succ]

/-- Against a fixed table, looking inputs up in the cache of a log returns their entries, and
charges one complete run per input missing from the log. -/
theorem run_simulateQ_counted_lookupAll (F : Q → α) (L : Set Q) {m : ℕ} (qs : Fin m → Q)
    (s : ℕ) :
    (simulateQ (coins (S := ℕ) + counted F) (lookupAll (cacheOf F L) qs)).run s =
      pure (fun i => F (qs i), s + missCount L qs) := by
  classical
  induction m generalizing s with
  | zero =>
    simp only [lookupAll, simulateQ_pure, StateT.run_pure, missCount, Nat.add_zero]
    congr
    funext i
    exact i.elim0
  | succ m ih =>
    by_cases hq : qs 0 ∈ L
    · have hc : cacheOf F L (qs 0) = some (F (qs 0)) := by simp [cacheOf, hq]
      simp only [lookupAll, hc, Option.elim, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, pure_bind, ih, missCount, hq, ite_true, Nat.zero_add]
      refine congrArg pure (Prod.ext ?_ rfl)
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    · have hc : cacheOf F L (qs 0) = none := by simp [cacheOf, hq]
      simp only [lookupAll, hc, Option.elim, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, QueryImpl.simulateQ_add_liftM_query_right, counted, StateT.run_modify,
        pure_bind, ih, missCount, hq, ite_false]
      refine congrArg pure (Prod.ext ?_ (by simp only; omega))
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

/-- The recovery step against a fixed table: on a successful output, the extractor receives the
table's entries at its points, and the counter grows by one complete run per point missing from
the log. -/
@[expose] noncomputable def recoverFrom {Out W : Type} {m : ℕ} (F : Q → α)
    (points : Out → Fin m → Q) (ext : Out → (Fin m → α) → ProbComp W)
    (z : (Option Out × Set Q) × ℕ) : ProbComp (Option W × ℕ) :=
  z.1.1.elim (pure (none, z.2)) fun o =>
    (fun w => (some w, z.2 + missCount z.1.2 (points o))) <$> ext o fun i => F (points o i)

variable [DecidableEq Q]

/-- Answer an acceptance query by a complete rerun, cache its output, and return its verdict. The
finder's coins pass through unchanged. -/
@[expose] def cachingImpl (accept : Q → α → Bool) :
    QueryImpl (unifSpec + rerunSpec Q Bool)
      (StateT (Q → Option α) (OracleComp (unifSpec + rerunSpec Q α))) :=
  (show QueryImpl unifSpec (StateT (Q → Option α) (OracleComp (unifSpec + rerunSpec Q α))) from
    fun n => liftM (liftM (unifSpec.query n) : OracleComp (unifSpec + rerunSpec Q α) _)) +
  (show QueryImpl (rerunSpec Q Bool)
      (StateT (Q → Option α) (OracleComp (unifSpec + rerunSpec Q α))) from fun q => do
    let a ← liftM (liftM ((rerunSpec Q α).query q) : OracleComp (unifSpec + rerunSpec Q α) α)
    modify fun cache => Function.update cache q (some a)
    pure (accept q a))

theorem run_cachingImpl_inl (accept : Q → α → Bool) (t : ℕ) (c : Q → Option α) :
    (cachingImpl accept (Sum.inl t)).run c =
      (liftM (unifSpec.query t) : OracleComp (unifSpec + rerunSpec Q α) _) >>=
        fun u => pure (u, c) := rfl

theorem run_cachingImpl_inr (accept : Q → α → Bool) (q : Q) (c : Q → Option α) :
    (cachingImpl accept (Sum.inr q)).run c =
      (liftM ((rerunSpec Q α).query q) : OracleComp (unifSpec + rerunSpec Q α) α) >>=
        fun a => pure (accept q a, Function.update c q (some a)) := by
  simp [cachingImpl]

/-- Run a finder against the verdicts of complete reruns, caching their outputs. On success,
recover the transcripts at the points of its output from the cache, and hand them to the
extractor. -/
@[expose] def recover {Out W : Type} {m : ℕ} (accept : Q → α → Bool)
    (find : OracleComp (unifSpec + rerunSpec Q Bool) (Option Out))
    (points : Out → Fin m → Q) (ext : Out → (Fin m → α) → ProbComp W) :
    OracleComp (unifSpec + rerunSpec Q α) (Option W) := do
  let z ← (simulateQ (cachingImpl accept) find).run fun _ => none
  z.1.elim (pure none) fun o => do
    let ts ← lookupAll z.2 (points o)
    some <$> OracleComp.liftComp (ext o ts) (unifSpec + rerunSpec Q α)

/-- Against a fixed table, the caching finder is the logged finder against the table's verdicts,
its cache holding the table's entries at the logged vectors. -/
theorem run_simulateQ_counted_caching (accept : Q → α → Bool) (F : Q → α) {β : Type}
    (oa : OracleComp (unifSpec + rerunSpec Q Bool) β) (L : Set Q) (n : ℕ) :
    (simulateQ (coins (S := ℕ) + counted F)
        ((simulateQ (cachingImpl accept) oa).run (cacheOf F L))).run n =
      (fun z => ((z.1, cacheOf F z.2.1), z.2.2)) <$>
        (simulateQ (coins (S := Set Q × ℕ) + logCounted fun q => accept q (F q)) oa).run
          (L, n) := by
  induction oa using OracleComp.inductionOn generalizing L n with
  | pure a => simp
  | query_bind q k ih =>
    cases q with
    | inl t =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl, StateT.run_bind,
        run_cachingImpl_inl, QueryImpl.simulateQ_add_liftM_query_left, bind_assoc, pure_bind]
      simp only [coins, QueryImpl.liftTarget_apply_run, QueryImpl.ofLift_apply, bind_map_left,
        map_bind]
      exact bind_congr fun a => ih a L n
    | inr q =>
      simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr, StateT.run_bind,
        run_cachingImpl_inr, QueryImpl.simulateQ_add_liftM_query_right, bind_assoc, pure_bind,
        counted, logCounted, StateT.run_modify]
      rw [update_cacheOf]
      exact ih _ _ _

/-- Against a fixed table, cached recovery is the logged finder against the table's verdicts,
followed by extraction from the table's entries at the output's points. -/
theorem run_simulateQ_counted_recover {Out W : Type} {m : ℕ} (accept : Q → α → Bool)
    (F : Q → α) (find : OracleComp (unifSpec + rerunSpec Q Bool) (Option Out))
    (points : Out → Fin m → Q) (ext : Out → (Fin m → α) → ProbComp W) :
    (simulateQ (coins (S := ℕ) + counted F) (recover accept find points ext)).run 0 =
      regroup <$> logRun (fun q => accept q (F q)) find >>= recoverFrom F points ext := by
  simp only [recover, simulateQ_bind, StateT.run_bind]
  rw [← cacheOf_empty F, run_simulateQ_counted_caching, bind_map_left, logRun, bind_map_left]
  refine bind_congr fun z => ?_
  obtain ⟨o?, L, n⟩ := z
  cases o? with
  | none => rfl
  | some o =>
    simp only [Option.elim, simulateQ_bind, StateT.run_bind, run_simulateQ_counted_lookupAll,
      pure_bind, simulateQ_map, StateT.run_map, QueryImpl.simulateQ_add_liftComp_left,
      recoverFrom, regroup]
    simp [coins]

end Cache

/-- The counted finder is the logged finder with its log forgotten. -/
theorem runFinder_eq_map_logRun {R : Type} {C : R → Type} {β : Type}
    (find : OracleComp (unifSpec + accSpec C) β) (g : ((r : R) → C r) → Bool) :
    runFinder find g = (fun z => (z.1, z.2.2)) <$> logRun g find :=
  (map_run_simulateQ_logCounted g find ∅ 0).symm

namespace ResetPolicy

variable {ι σ : Type} {spec : OracleSpec ι} {init : ProbComp σ}
  {impl : QueryImpl spec (StateT σ ProbComp)} (P : ResetPolicy init impl)
  {R : Type} {C : R → Type}

/-- Against frozen reruns, recovery is the logged finder against the verdicts of an eager table of
complete outputs, followed by extraction from the same table, with the same complete-run count. -/
theorem attempt_recover {Q α Out W : Type} [Finite Q] [DecidableEq Q] {m : ℕ}
    (run : Q → OracleComp spec α) (accept : Q → α → Bool)
    (find : OracleComp (unifSpec + rerunSpec Q Bool) (Option Out))
    (points : Out → Fin m → Q) (ext : Out → (Fin m → α) → ProbComp W) :
    P.attempt run (recover accept find points ext) =ᵈ
      (do let F ← P.eagerTable run
          regroup <$> logRun (fun q => accept q (F q)) find >>= recoverFrom F points ext) := by
  simpa only [run_simulateQ_counted_recover] using
    P.attempt_eagerTable run (recover accept find points ext)

/-- A finder's affine success bound and its cost transfer to recovery against frozen reruns, with
no further complete runs: every point of a good output was queried, so its transcript is cached.
If the extractor returns a valid witness from every good output's transcripts, a valid witness
comes back with the finder's success guarantee. -/
theorem recover_bounds [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    [DecidableEq ((r : R) → C r)] {α Out W : Type}
    (run : ((r : R) → C r) → OracleComp spec α) (accept : ((r : R) → C r) → α → Bool)
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) {m : ℕ} (points : Out → Fin m → ((r : R) → C r))
    (hpts : ∀ f o, good f o → ∀ i, f (points o i) = true)
    (ext : Out → (Fin m → α) → ProbComp W) (valid : W → Prop)
    (hext : ∀ F ∈ support (P.eagerTable run), ∀ o, good (fun c => accept c (F c)) o →
      ∀ w ∈ support (ext o fun i => F (points o i)), valid w) :
    (∑ c, Pr{let a ← (do (simulateQ impl (run c)).run' (← init))}[accept c a = true]) /
        Fintype.card ((r : R) → C r) ≤
      κ + (1 - κ) * Pr{let z ← P.attempt run (recover accept find points ext)}[
        ∃ w, z.1 = some w ∧ valid w] ∧
    expectedCalls (P.attempt run (recover accept find points ext)) ≤ T := by
  classical
  have hlaw := P.attempt_recover run accept find points ext
  have hmarg : ∀ c, ((fun f => f c) <$> ((fun F c => accept c (F c)) <$> P.eagerTable run)) =ᵈ
      (accept c <$> (do (simulateQ impl (run c)).run' (← init))) := by
    intro c
    have h1 : ((fun f => f c) <$> ((fun F c => accept c (F c)) <$> P.eagerTable run)) =
        accept c <$> ((fun F => F c) <$> P.eagerTable run) := by
      simp only [Functor.map_map]
    rw [h1]
    exact EvalDistEq.map_congr (accept c) (P.eagerTable_marginal run c)
  have hacc : averageAcceptRate ((fun F c => accept c (F c)) <$> P.eagerTable run) =
      (∑ c, Pr{let a ← (do (simulateQ impl (run c)).run' (← init))}[accept c a = true]) /
        Fintype.card ((r : R) → C r) := by
    rw [averageAcceptRate_eq_of_marginals hmarg]
    simp only [prEvent_map]
  have hsucc :
      Pr{let z ← ((fun (F : ((r : R) → C r) → α) c => accept c (F c)) <$> P.eagerTable run >>=
          fun f => runFinder find f)}[z.1.isSome] ≤
        Pr{let z ← P.attempt run (recover accept find points ext)}[
          ∃ w, z.1 = some w ∧ valid w] := by
    rw [hlaw.prEvent_eq, bind_map_left]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun F hF => ?_
    rw [runFinder_eq_map_logRun, prEvent_map, bind_map_left]
    refine prEvent_le_prEvent_bind_of_support _ _ _ _ fun z hz hsome => ?_
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
    have hcount : (z.1, z.2.2) ∈ support (runFinder find (fun c => accept c (F c))) := by
      rw [runFinder_eq_map_logRun, support_map]
      exact ⟨z, hz, rfl⟩
    have hgood := h.sound _ _ hcount o ho
    apply prEvent_eq_one_of_forall_mem_support
    intro y hy
    obtain ⟨o?, L, n⟩ := z
    simp only at ho
    subst ho
    simp only [regroup, recoverFrom, Option.elim, support_map, Set.mem_image] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨w, rfl, hext F hF o hgood w hw⟩
  have hcost : expectedCalls (P.attempt run (recover accept find points ext)) ≤ T := by
    rw [expectedCalls_eq_of_evalDistEq hlaw]
    let : MeasurableSpace (((r : R) → C r) → α) := ⊤
    rw [expectedCalls_bind]
    calc
      (∫⁻ F, expectedCalls (regroup <$> logRun (fun q => accept q (F q)) find >>=
            recoverFrom F points ext) ∂𝒟[P.eagerTable run]) ≤
          ∫⁻ _F, T ∂𝒟[P.eagerTable run] := by
        refine lintegral_mono fun F => ?_
        refine (expectedCalls_bind_le_add _ _ 0 fun z hz y hy => ?_).trans ?_
        · rw [support_map] at hz
          obtain ⟨z', hz', rfl⟩ := hz
          obtain ⟨o?, L, n⟩ := z'
          cases o? with
          | none =>
            simp only [regroup, recoverFrom, Option.elim, support_pure,
              Set.mem_singleton_iff] at hy
            simp [hy, regroup]
          | some o =>
            simp only [regroup, recoverFrom, Option.elim, support_map,
              Set.mem_image] at hy
            obtain ⟨w, -, rfl⟩ := hy
            rw [missCount_eq_zero L (points o)
              fun i => h.mem_log_of_mem_support points hpts _ _ hz' o rfl i]
            simp [regroup]
        · rw [Nat.cast_zero, add_zero, ← expectedCalls_map_output Prod.fst]
          have hmap : (fun y => (y.1.1, y.2)) <$>
              (regroup <$> logRun (fun q => accept q (F q)) find) =
                runFinder find fun c => accept c (F c) := by
            rw [runFinder_eq_map_logRun, Functor.map_map]
            rfl
          rw [hmap]
          exact h.cost _
      _ = T * 𝒟[P.eagerTable run] Set.univ := lintegral_const _
      _ ≤ T := mul_le_of_le_one_right zero_le (evalDist_apply_univ_le_one _)
  refine ⟨?_, hcost⟩
  rw [← hacc]
  calc
    averageAcceptRate ((fun F c => accept c (F c)) <$> P.eagerTable run) ≤
        κ + (1 - κ) *
          Pr{let z ← ((fun (F : ((r : R) → C r) → α) c => accept c (F c)) <$> P.eagerTable run >>=
            fun f => runFinder find f)}[z.1.isSome] :=
      h.average_success _
    _ ≤ _ := by gcongr

/-- `ResetPolicy.recover_bounds` with the subtractive success bound. -/
theorem recover_bounds_sub [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    [DecidableEq ((r : R) → C r)] {α Out W : Type}
    (run : ((r : R) → C r) → OracleComp spec α) (accept : ((r : R) → C r) → α → Bool)
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) {m : ℕ} (points : Out → Fin m → ((r : R) → C r))
    (hpts : ∀ f o, good f o → ∀ i, f (points o i) = true)
    (ext : Out → (Fin m → α) → ProbComp W) (valid : W → Prop)
    (hext : ∀ F ∈ support (P.eagerTable run), ∀ o, good (fun c => accept c (F c)) o →
      ∀ w ∈ support (ext o fun i => F (points o i)), valid w) :
    (∑ c, Pr{let a ← (do (simulateQ impl (run c)).run' (← init))}[accept c a = true]) /
        Fintype.card ((r : R) → C r) - κ ≤
      Pr{let z ← P.attempt run (recover accept find points ext)}[
        ∃ w, z.1 = some w ∧ valid w] ∧
    expectedCalls (P.attempt run (recover accept find points ext)) ≤ T := by
  obtain ⟨hs, hc⟩ := P.recover_bounds run accept h points hpts ext valid hext
  exact ⟨tsub_le_iff_left.mpr
    (hs.trans (add_le_add le_rfl (mul_le_of_le_one_left zero_le tsub_le_self))), hc⟩

end ResetPolicy

end Rewinding
