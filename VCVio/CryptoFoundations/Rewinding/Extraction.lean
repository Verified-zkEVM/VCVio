/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.Rewinding.FinderBridge
public import VCVio.CryptoFoundations.Rewinding.ThresholdSemantics

/-!
# Recovering transcripts from a finder

A finder (`Rewinding.IsFinder`) sees only the verdicts of complete runs. To extract a witness, the
transcripts at the challenges of its output are needed as well. `Rewinding.recover` runs a finder
against the verdicts of frozen reruns, reruns every point of a successful output to recover its
transcript, and hands the transcripts to an extractor.

Against a fixed table of complete outputs, the recovered transcripts are the table's entries at the
output's points (`Rewinding.run_simulateQ_counted_recover`), so they are exactly the runs whose
verdicts the finder saw. Against frozen reruns, the eager representation
(`Rewinding.ResetPolicy.attempt_eagerTable`) carries this over, and the finder's success and cost
bounds become an extractor's (`Rewinding.ResetPolicy.recover_bounds`).

## Main definitions

* `Rewinding.verdictImpl`: answer an acceptance query with the verdict of a complete rerun.
* `Rewinding.rerunAll`: rerun each of finitely many inputs.
* `Rewinding.recover`: find, recover the transcripts at the output's points, extract.

## Main results

* `Rewinding.ResetPolicy.eagerTable_settled`: every table in the eager table's support is settled
  in one world.
* `Rewinding.ResetPolicy.eagerTable_fst_eq`: runs that share a first phase give one public value
  in every table, as a Σ-protocol's commitment.
* `Rewinding.ResetPolicy.attempt_recover`: against frozen reruns, recovery is the finder against
  the verdicts of an eager table, followed by extraction from the same table.
* `Rewinding.ResetPolicy.recover_bounds`: the finder's affine success bound and its cost, plus
  the replays, transfer to the extractor.
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

/-! ## Recovery against a fixed table -/

section Recover

variable {Q α : Type}

/-- Answer an acceptance query with the verdict of a complete rerun. The finder's coins pass
through unchanged. -/
@[expose] def verdictImpl (accept : Q → α → Bool) :
    QueryImpl (unifSpec + rerunSpec Q Bool) (OracleComp (unifSpec + rerunSpec Q α)) :=
  (show QueryImpl unifSpec (OracleComp (unifSpec + rerunSpec Q α)) from
    fun n => liftM (unifSpec.query n)) +
  (show QueryImpl (rerunSpec Q Bool) (OracleComp (unifSpec + rerunSpec Q α)) from
    fun q => accept q <$> liftM ((rerunSpec Q α).query q))

/-- Rerun each of finitely many inputs once, in order. -/
@[expose] def rerunAll : {m : ℕ} → (Fin m → Q) → OracleComp (unifSpec + rerunSpec Q α) (Fin m → α)
  | 0, _ => pure Fin.elim0
  | _ + 1, qs => do
      let a ← liftM ((rerunSpec Q α).query (qs 0))
      let ts ← rerunAll (Fin.tail qs)
      pure (Fin.cons a ts)

/-- Run a finder against the verdicts of complete reruns. On success, rerun every point of its
output to recover the transcripts, and hand them to the extractor. -/
@[expose] def recover {Out W : Type} {m : ℕ} (accept : Q → α → Bool)
    (find : OracleComp (unifSpec + rerunSpec Q Bool) (Option Out))
    (points : Out → Fin m → Q) (ext : Out → (Fin m → α) → ProbComp W) :
    OracleComp (unifSpec + rerunSpec Q α) (Option W) := do
  let o? ← simulateQ (verdictImpl accept) find
  o?.elim (pure none) fun o => do
    let ts ← rerunAll (points o)
    some <$> OracleComp.liftComp (ext o ts) (unifSpec + rerunSpec Q α)

/-- Against a fixed table of complete outputs, the finder answered by verdicts of reruns is the
finder against the table's verdicts. -/
theorem simulateQ_counted_verdictImpl (accept : Q → α → Bool) (F : Q → α) {β : Type}
    (find : OracleComp (unifSpec + rerunSpec Q Bool) β) :
    simulateQ (coins (S := ℕ) + counted F) (simulateQ (verdictImpl accept) find) =
      simulateQ (coins (S := ℕ) + counted fun q => accept q (F q)) find := by
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => by cases t <;> rfl) find

/-- Against a fixed table, rerunning finitely many inputs returns their entries and charges one
complete run each. -/
theorem run_simulateQ_counted_rerunAll (F : Q → α) {m : ℕ} (qs : Fin m → Q) (s : ℕ) :
    (simulateQ (coins (S := ℕ) + counted F) (rerunAll qs)).run s =
      pure (fun i => F (qs i), s + m) := by
  induction m generalizing s with
  | zero =>
    simp only [rerunAll, simulateQ_pure, StateT.run_pure, Nat.add_zero]
    congr
    funext i
    exact i.elim0
  | succ m ih =>
    simp only [rerunAll, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      QueryImpl.simulateQ_add_liftM_query_right, counted, StateT.run_modify, pure_bind, ih]
    refine congrArg pure (Prod.ext ?_ (by simp only; omega))
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- The recovery step against a fixed table: on a successful output, the extractor receives the
table's entries at its points, and the counter grows by one complete run per point. -/
@[expose] def recoverFrom {Out W : Type} {m : ℕ} (F : Q → α) (points : Out → Fin m → Q)
    (ext : Out → (Fin m → α) → ProbComp W) (z : Option Out × ℕ) : ProbComp (Option W × ℕ) :=
  z.1.elim (pure (none, z.2)) fun o =>
    (fun w => (some w, z.2 + m)) <$> ext o fun i => F (points o i)

/-- Against a fixed table, recovery is the finder against the table's verdicts, followed by
extraction from the table's entries at the output's points. -/
theorem run_simulateQ_counted_recover {Out W : Type} {m : ℕ} (accept : Q → α → Bool)
    (F : Q → α) (find : OracleComp (unifSpec + rerunSpec Q Bool) (Option Out))
    (points : Out → Fin m → Q) (ext : Out → (Fin m → α) → ProbComp W) :
    (simulateQ (coins (S := ℕ) + counted F) (recover accept find points ext)).run 0 =
      (simulateQ (coins (S := ℕ) + counted fun q => accept q (F q)) find).run 0 >>=
        recoverFrom F points ext := by
  simp only [recover, simulateQ_bind, StateT.run_bind, simulateQ_counted_verdictImpl]
  refine bind_congr fun z => ?_
  obtain ⟨o?, n⟩ := z
  cases o? with
  | none => rfl
  | some o =>
    simp only [Option.elim, simulateQ_bind, StateT.run_bind, run_simulateQ_counted_rerunAll,
      pure_bind, simulateQ_map, StateT.run_map, QueryImpl.simulateQ_add_liftComp_left, recoverFrom]
    simp [coins]

end Recover

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

/-! ## Recovery against frozen reruns -/

namespace ResetPolicy

variable {ι σ : Type} {spec : OracleSpec ι} {init : ProbComp σ}
  {impl : QueryImpl spec (StateT σ ProbComp)} (P : ResetPolicy init impl)

/-- Against frozen reruns, recovery is the finder against the verdicts of an eager table of
complete outputs, followed by extraction from the same table, with the same complete-run count. -/
theorem attempt_recover {Q α Out W : Type} [Finite Q] {m : ℕ} (run : Q → OracleComp spec α)
    (accept : Q → α → Bool) (find : OracleComp (unifSpec + rerunSpec Q Bool) (Option Out))
    (points : Out → Fin m → Q) (ext : Out → (Fin m → α) → ProbComp W) :
    P.attempt run (recover accept find points ext) =ᵈ
      (do let F ← P.eagerTable run
          (simulateQ (coins (S := ℕ) + counted fun q => accept q (F q)) find).run 0 >>=
            recoverFrom F points ext) := by
  simpa only [run_simulateQ_counted_recover] using
    P.attempt_eagerTable run (recover accept find points ext)

variable {R : Type} {C : R → Type}

/-- A finder's affine success bound and cost transfer to recovery against frozen reruns. If the
extractor returns a valid witness from every good output's transcripts, a valid witness comes
back with the finder's success guarantee, and the expected number of complete runs is the
finder's cost plus one replay per point. -/
theorem recover_bounds [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)] {α Out W : Type}
    (run : ((r : R) → C r) → OracleComp spec α) (accept : ((r : R) → C r) → α → Bool)
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) {m : ℕ} (points : Out → Fin m → ((r : R) → C r))
    (ext : Out → (Fin m → α) → ProbComp W) (valid : W → Prop)
    (hext : ∀ F ∈ support (P.eagerTable run), ∀ o, good (fun c => accept c (F c)) o →
      ∀ w ∈ support (ext o fun i => F (points o i)), valid w) :
    (∑ c, Pr{let a ← (do (simulateQ impl (run c)).run' (← init))}[accept c a = true]) /
        Fintype.card ((r : R) → C r) ≤
      κ + (1 - κ) *
        Pr{let z ← P.attempt run (recover accept find points ext)}[∃ w, z.1 = some w ∧ valid w] ∧
    expectedCalls (P.attempt run (recover accept find points ext)) ≤ T + m := by
  classical
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
    rw [(P.attempt_recover run accept find points ext).prEvent_eq, bind_map_left]
    refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun F hF => ?_
    refine prEvent_le_prEvent_bind_of_support _ _ _ _ fun z hz hsome => ?_
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
    have hgood := h.sound _ z hz o ho
    apply prEvent_eq_one_of_forall_mem_support
    intro y hy
    obtain ⟨o?, n⟩ := z
    simp only at ho
    subst ho
    simp only [recoverFrom, Option.elim, support_map, Set.mem_image] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨w, rfl, hext F hF o hgood w hw⟩
  have hcost : expectedCalls (P.attempt run (recover accept find points ext)) ≤ T + m := by
    rw [expectedCalls_eq_of_evalDistEq (P.attempt_recover run accept find points ext)]
    let : MeasurableSpace (((r : R) → C r) → α) := ⊤
    rw [expectedCalls_bind]
    calc
      (∫⁻ F, expectedCalls ((simulateQ (coins (S := ℕ) + counted fun q => accept q (F q))
            find).run 0 >>= recoverFrom F points ext) ∂𝒟[P.eagerTable run]) ≤
          ∫⁻ _F, (T + m) ∂𝒟[P.eagerTable run] := by
        refine lintegral_mono fun F => ?_
        refine (expectedCalls_bind_le_add _ _ m fun z _ y hy => ?_).trans
          (add_le_add (h.cost _) le_rfl)
        obtain ⟨o?, n⟩ := z
        cases o? with
        | none =>
          simp only [recoverFrom, Option.elim, support_pure, Set.mem_singleton_iff] at hy
          simp [hy]
        | some o =>
          simp only [recoverFrom, Option.elim, support_map, Set.mem_image] at hy
          obtain ⟨w, -, rfl⟩ := hy
          exact le_rfl
      _ = (T + m) * 𝒟[P.eagerTable run] Set.univ := lintegral_const _
      _ ≤ T + m := mul_le_of_le_one_right zero_le (evalDist_apply_univ_le_one _)
  refine ⟨?_, hcost⟩
  rw [← hacc]
  calc
    averageAcceptRate ((fun F c => accept c (F c)) <$> P.eagerTable run) ≤
        κ + (1 - κ) *
          Pr{let z ← ((fun (F : ((r : R) → C r) → α) c => accept c (F c)) <$> P.eagerTable run >>=
            fun f => runFinder find f)}[z.1.isSome] :=
      h.average_success _
    _ ≤ _ := by gcongr

/-- `ResetPolicy.recover_bounds` with the subtractive success bound: a valid witness comes back
with probability at least the honest acceptance probability, averaged over complete challenge
vectors, minus the finder's error. -/
theorem recover_bounds_sub [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)] {α Out W : Type}
    (run : ((r : R) → C r) → OracleComp spec α) (accept : ((r : R) → C r) → α → Bool)
    {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) {m : ℕ} (points : Out → Fin m → ((r : R) → C r))
    (ext : Out → (Fin m → α) → ProbComp W) (valid : W → Prop)
    (hext : ∀ F ∈ support (P.eagerTable run), ∀ o, good (fun c => accept c (F c)) o →
      ∀ w ∈ support (ext o fun i => F (points o i)), valid w) :
    (∑ c, Pr{let a ← (do (simulateQ impl (run c)).run' (← init))}[accept c a = true]) /
        Fintype.card ((r : R) → C r) - κ ≤
      Pr{let z ← P.attempt run (recover accept find points ext)}[∃ w, z.1 = some w ∧ valid w] ∧
    expectedCalls (P.attempt run (recover accept find points ext)) ≤ T + m := by
  obtain ⟨hs, hc⟩ := P.recover_bounds run accept h points ext valid hext
  exact ⟨tsub_le_iff_left.mpr
    (hs.trans (add_le_add le_rfl (mul_le_of_le_one_left zero_le tsub_le_self))), hc⟩

end ResetPolicy

end Rewinding
