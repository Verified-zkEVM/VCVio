/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.CryptoFoundations.Rewinding.FinderBridge
public import VCVio.OracleComp.QueryTracking.CostModel

/-!
# Charged reruns

`Rewinding.counted` charges one unit per complete rerun, so the cost field of
`Rewinding.IsFinder` bounds the expected number of complete reruns. `Rewinding.charged` answers
in the same way and charges an arbitrary per-input cost instead. `Rewinding.expectedCalls` is the
expectation of the natural-valued counter, so for a charged run it is the expected accumulated
charge.

* `Rewinding.expectedCalls_runCharged_le`: if every rerun costs at most `c`, the expected
  accumulated charge is at most `c` times the expected number of reruns.
* `Rewinding.IsFinder.expectedCalls_runCharged_le`: hence at most `c * T` for a finder of cost
  `T`.
* `Rewinding.IsFinder.expectedCalls_bind_runCharged_le_lintegral_sup_mul`: against a randomly drawn
  answer and cost table, at most `T` times the expected largest rerun cost of the table;
  `Rewinding.IsFinder.expectedCalls_bind_runCharged_le` is its worst case `c * T` when every
  rerun of every table in the support costs at most `c`.
* `Rewinding.costAdapter`: an algorithm run against reruns that report their own cost, with the
  reported costs accumulated beside its output.
* `Rewinding.ResetPolicy.chargedAttempt`: an attempt against frozen reruns, each reporting its
  oracle-query cost under a cost model through `instrumentedRun`. Forgetting the accumulated cost
  gives the uninstrumented attempt (`Rewinding.ResetPolicy.map_chargedAttempt_eq_attempt`).
* `Rewinding.ResetPolicy.expectedCalls_fst_attempt_costAdapter_le_lintegral_sup_mul`: against frozen
  reruns that report their own cost, a finder of cost `T` has expected accumulated reported cost
  at most `T` times the expected largest rerun cost of the eager table.
* `Rewinding.ResetPolicy.cost_le_mul_runs_of_mem_support_chargedAttempt`: on every outcome, the
  accumulated query cost is at most `c` times the number of complete runs when every complete run
  has worst-case query cost at most `c`.
* `Rewinding.ResetPolicy.finder_bounds_charged_of_worstCaseCostBound`: one charged attempt
  satisfies the bounds of `Rewinding.ResetPolicy.finder_bounds` and the expected query-cost bound
  `c * T` when every complete run has worst-case query cost at most `c`.

## Accounting boundary

A rerun on input `q` executes the supplied computation `run q` from its beginning, and that
computation defines the accounting boundary. Instrumentation records the oracle queries present in
`run q` at the prices of the supplied cost model, which may be zero. To charge both sides of an
interaction, supply the complete interaction, including the verifier side, as `run q`; nothing here
checks that it is complete. The charge excludes the reset policy's work to answer those queries,
local computation, and the black-box algorithm's own work and coin queries. Under
`Rewinding.fixedTape` the oracle queries of `run q` are its private coin draws, so the query cost
counts coin draws: a rerun that replays a draw from the frozen tape is charged for it again.
When a complete run simulates a computation through stateless handlers, and every complete
handler call has target cost at most the charge that the source cost model assigns to its query,
`WorstCaseCostBound.simulateQ` gives the run's worst-case query cost from the computation's budget.

The bounds use, in each frozen world, the largest rerun cost over all inputs. The expectation of
that maximum over the worlds suffices. A bound uniform over worlds and inputs gives the worst-case
corollaries. An expected cost of each input's rerun, averaged over the worlds, does not suffice
under the `Rewinding.IsFinder` contract: a finder may choose its inputs after observing the frozen
world, and so select the expensive reruns.

`Rewinding.ResetPolicy.cost_le_mul_runs_of_mem_support_chargedAttempt` is the pathwise form of
these bounds.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Rewinding

/-! ## Charged reruns -/

/-- Answer from a fixed function and charge `cost q` for the complete run on input `q`. -/
@[expose, simps] def charged {Q α : Type} (f : Q → α) (cost : Q → ℕ) :
    QueryImpl (rerunSpec Q α) (StateT ℕ ProbComp) where
  toFun q := do
    modify (· + cost q)
    pure (f q)

/-- Run a black-box algorithm against a fixed answer table, charging `cost q` for each rerun on
input `q`, from the initial counter `s`. -/
@[expose] def runCharged {Q α β : Type} (alg : OracleComp (unifSpec + rerunSpec Q α) β)
    (f : Q → α) (cost : Q → ℕ) (s : ℕ) : ProbComp (β × ℕ) :=
  (simulateQ (coins (S := ℕ) + charged f cost) alg).run s

/-- A finder's run is its charged run at unit cost from the zero counter. -/
theorem runFinder_eq_runCharged {R : Type} {C : R → Type} {β : Type}
    (find : OracleComp (unifSpec + accSpec C) β) (f : ((r : R) → C r) → Bool) :
    runFinder find f = runCharged find f (fun _ => 1) 0 :=
  rfl

/-- A pure algorithm returns its output with the initial counter. -/
@[simp]
theorem runCharged_pure {Q α β : Type} (b : β) (f : Q → α) (cost : Q → ℕ) (s : ℕ) :
    runCharged (pure b : OracleComp (unifSpec + rerunSpec Q α) β) f cost s = pure (b, s) := by
  simp [runCharged]

/-- A coin query of a charged run is a fresh coin, with no charge. -/
theorem runCharged_query_inl_bind {Q α β : Type} (n : ℕ)
    (k : (unifSpec + rerunSpec Q α).Range (Sum.inl n) → OracleComp (unifSpec + rerunSpec Q α) β)
    (f : Q → α) (cost : Q → ℕ) (s : ℕ) :
    runCharged (liftM ((unifSpec + rerunSpec Q α).query (Sum.inl n)) >>= k) f cost s =
      (query (spec := unifSpec) n : ProbComp _) >>= fun u => runCharged (k u) f cost s := by
  simp [runCharged, coins]

/-- A rerun on `q` in a charged run answers from the table and charges `cost q`. -/
theorem runCharged_query_inr_bind {Q α β : Type} (q : Q)
    (k : (unifSpec + rerunSpec Q α).Range (Sum.inr q) → OracleComp (unifSpec + rerunSpec Q α) β)
    (f : Q → α) (cost : Q → ℕ) (s : ℕ) :
    runCharged (liftM ((unifSpec + rerunSpec Q α).query (Sum.inr q)) >>= k) f cost s =
      runCharged (k (f q)) f cost (s + cost q) := by
  simp [runCharged, charged_apply]

/-- If every rerun costs at most `c`, the expected accumulated charge of a run is at most `c`
times its expected number of reruns, for initial counters `s₁ ≤ c * s₂`. -/
theorem expectedCalls_runCharged_le {Q α β : Type}
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (f : Q → α) (cost : Q → ℕ) (c : ℕ)
    (hc : ∀ q, cost q ≤ c) (s₁ s₂ : ℕ) (hs : s₁ ≤ c * s₂) :
    expectedCalls (runCharged alg f cost s₁) ≤
      c * expectedCalls (runCharged alg f (fun _ => 1) s₂) := by
  induction alg using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure b =>
    rw [runCharged_pure, runCharged_pure, expectedCalls_pure, expectedCalls_pure]
    exact_mod_cast hs
  | query_bind t k ih =>
    rcases t with n | q
    · let : MeasurableSpace (Fin (n + 1)) := ⊤
      rw [runCharged_query_inl_bind, runCharged_query_inl_bind, expectedCalls_bind,
        expectedCalls_bind, ← lintegral_const_mul _ Measurable.of_discrete]
      exact lintegral_mono fun u => ih u s₁ s₂ hs
    · rw [runCharged_query_inr_bind, runCharged_query_inr_bind]
      exact ih _ _ _ (by rw [mul_add, mul_one]; exact add_le_add hs (hc q))

/-- A finder of cost `T` whose reruns each cost at most `c` has expected accumulated charge at
most `c * T` against every acceptance function. -/
theorem IsFinder.expectedCalls_runCharged_le {R : Type} [Fintype R] [DecidableEq R]
    {C : R → Type} [∀ r, Fintype (C r)]
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) (f : ((r : R) → C r) → Bool)
    (cost : ((r : R) → C r) → ℕ) (c : ℕ) (hc : ∀ q, cost q ≤ c) :
    expectedCalls (runCharged find f cost 0) ≤ c * T :=
  (Rewinding.expectedCalls_runCharged_le find f cost c hc 0 0 (Nat.zero_le _)).trans
    (by rw [← runFinder_eq_runCharged]; gcongr; exact h.cost f)

/-- A finder of cost `T` against a randomly drawn acceptance and cost table has expected
accumulated charge at most `T` times the expected largest rerun cost of the table. -/
theorem IsFinder.expectedCalls_bind_runCharged_le_lintegral_sup_mul {R : Type} [Fintype R]
    [DecidableEq R] {C : R → Type} [∀ r, Fintype (C r)]
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) {W : Type} [MeasurableSpace W] [DiscreteMeasurableSpace W]
    (F : ProbComp W) (acc : W → ((r : R) → C r) → Bool) (cost : W → ((r : R) → C r) → ℕ) :
    expectedCalls (do let w ← F; runCharged find (acc w) (cost w) 0) ≤
      (∫⁻ w, ((Finset.univ.sup (cost w) : ℕ) : ℝ≥0∞) ∂𝒟[F]) * T := by
  rw [expectedCalls_bind, ← lintegral_mul_const _ Measurable.of_discrete]
  exact lintegral_mono fun w =>
    h.expectedCalls_runCharged_le _ _ _ fun q => Finset.le_sup (Finset.mem_univ q)

/-- A finder of cost `T` against a randomly drawn acceptance and cost table has expected
accumulated charge at most `c * T`, provided every rerun costs at most `c` for every table in the
support and every input. -/
theorem IsFinder.expectedCalls_bind_runCharged_le {R : Type} [Fintype R] [DecidableEq R]
    {C : R → Type} [∀ r, Fintype (C r)]
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) {W : Type} (F : ProbComp W)
    (acc : W → ((r : R) → C r) → Bool) (cost : W → ((r : R) → C r) → ℕ) (c : ℕ)
    (hc : ∀ w ∈ support F, ∀ q, cost w q ≤ c) :
    expectedCalls (do let w ← F; runCharged find (acc w) (cost w) 0) ≤ c * T := by
  let : MeasurableSpace W := ⊤
  refine (h.expectedCalls_bind_runCharged_le_lintegral_sup_mul F acc cost).trans ?_
  gcongr
  calc (∫⁻ w, ((Finset.univ.sup (cost w) : ℕ) : ℝ≥0∞) ∂𝒟[F])
      ≤ ∫⁻ _w, (c : ℝ≥0∞) ∂𝒟[F] :=
        lintegral_mono_ae (evalDist.ae_of_forall_mem_support F _ MeasurableSet.of_discrete
          fun w hw => by exact_mod_cast Finset.sup_le fun q _ => hc w hw q)
    _ = c * 𝒟[F] Set.univ := lintegral_const _
    _ ≤ c * 1 := by gcongr; exact evalDist_apply_univ_le_one F
    _ = c := mul_one _

/-! ## Reruns that report their own cost -/

/-- Answer coin queries by coin queries, and a rerun on `q` by a rerun that also reports its cost,
adding the reported cost to the state. -/
@[expose, simps] def costAdapterImpl {Q α : Type} :
    QueryImpl (unifSpec + rerunSpec Q α)
      (StateT ℕ (OracleComp (unifSpec + rerunSpec Q (α × ℕ)))) where
  toFun
  | Sum.inl n =>
    (liftM ((unifSpec + rerunSpec Q (α × ℕ)).query (Sum.inl n)) :
      StateT ℕ (OracleComp (unifSpec + rerunSpec Q (α × ℕ))) (Fin (n + 1)))
  | Sum.inr q => do
    let z ← (liftM ((unifSpec + rerunSpec Q (α × ℕ)).query (Sum.inr q)) :
      StateT ℕ (OracleComp (unifSpec + rerunSpec Q (α × ℕ))) (α × ℕ))
    modify (· + z.2)
    pure z.1

/-- Run `alg` against reruns that report their own cost, returning its output and the sum of the
reported costs. -/
@[expose] def costAdapter {Q α β : Type} (alg : OracleComp (unifSpec + rerunSpec Q α) β) :
    OracleComp (unifSpec + rerunSpec Q (α × ℕ)) (β × ℕ) :=
  (simulateQ costAdapterImpl alg).run 0

private theorem fst_map_simulateQ_counted_costAdapterImpl {Q α β : Type} (g : Q → α × ℕ)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (s m : ℕ) :
    Prod.fst <$>
        (simulateQ (coins (S := ℕ) + counted g) ((simulateQ costAdapterImpl alg).run s)).run m =
      runCharged alg (fun q => (g q).1) (fun q => (g q).2) s := by
  induction alg using OracleComp.inductionOn generalizing s m with
  | pure b => simp [runCharged]
  | query_bind t k ih =>
    rcases t with n | q
    · rw [runCharged_query_inl_bind]
      simp only [coins, QueryImpl.ofLift_eq_id'] at ih ⊢
      simp [costAdapterImpl_apply, ih]
    · rw [runCharged_query_inr_bind]
      simpa [costAdapterImpl_apply, coins, counted_apply] using ih _ _ _

/-- Against a fixed table of answers and costs, the output and accumulated reported cost of
`costAdapter alg` form the charged run of `alg`. -/
theorem fst_map_simulateQ_counted_costAdapter {Q α β : Type} (g : Q → α × ℕ)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (m : ℕ) :
    Prod.fst <$> (simulateQ (coins (S := ℕ) + counted g) (costAdapter alg)).run m =
      runCharged alg (fun q => (g q).1) (fun q => (g q).2) 0 :=
  fst_map_simulateQ_counted_costAdapterImpl g alg 0 m

/-- Against a fixed table of answers and costs, the output and rerun count of `costAdapter alg`
are those of `alg` against the answers alone. -/
theorem map_simulateQ_counted_costAdapter {Q α β : Type} (g : Q → α × ℕ)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (m : ℕ) :
    (fun z => (z.1.1, z.2)) <$> (simulateQ (coins (S := ℕ) + counted g) (costAdapter alg)).run m =
      (simulateQ (coins (S := ℕ) + counted (fun q => (g q).1)) alg).run m := by
  unfold costAdapter
  generalize (0 : ℕ) = s
  induction alg using OracleComp.inductionOn generalizing s m with
  | pure b => simp
  | query_bind t k ih =>
    rcases t with n | q
    · simp only [coins, QueryImpl.ofLift_eq_id'] at ih ⊢
      simp [costAdapterImpl_apply, ih]
    · simpa [costAdapterImpl_apply, coins, counted_apply] using ih _ _ _

/-! ## Frozen reruns that report their own cost -/

private theorem fst_map_runAdd_instrumentedRun {ι : Type} {spec : OracleSpec ι} {α : Type}
    (oa : OracleComp spec α) (cm : CostModel spec ℕ) :
    Prod.fst <$> (instrumentedRun oa cm).runAdd = oa :=
  (AddWriterT.fst_map_runAdd _).trans (fst_map_costDist oa cm)

namespace ResetPolicy

variable {R : Type} {C : R → Type}
variable {ι σ : Type} {spec : OracleSpec ι} {init : ProbComp σ}
  {impl : QueryImpl spec (StateT σ ProbComp)} (P : ResetPolicy init impl)

/-- An attempt of `alg` against frozen reruns of `run`, each instrumented to report its
oracle-query cost under `cm`. It returns the output of `alg` with the accumulated query cost, and
the number of complete runs. -/
@[expose] def chargedAttempt {Q α β : Type} (run : Q → OracleComp spec α)
    (cm : CostModel spec ℕ) (alg : OracleComp (unifSpec + rerunSpec Q α) β) :
    ProbComp ((β × ℕ) × ℕ) :=
  P.attempt (fun q => (instrumentedRun (run q) cm).runAdd) (costAdapter alg)

private theorem map_run_simulateQ_rerun_costAdapterImpl {Q α β : Type}
    (run : Q → OracleComp spec (α × ℕ)) (alg : OracleComp (unifSpec + rerunSpec Q α) β)
    (s : ℕ) (st : P.World × ℕ) :
    (fun z : (β × ℕ) × (P.World × ℕ) => (z.1.1, z.2)) <$>
        (simulateQ (coins (S := P.World × ℕ) + P.rerun run)
          ((simulateQ costAdapterImpl alg).run s)).run st =
      (simulateQ (coins (S := P.World × ℕ) + P.rerun (fun q => Prod.fst <$> run q)) alg).run
        st := by
  induction alg using OracleComp.inductionOn generalizing s st with
  | pure b => simp
  | query_bind t k ih =>
    rcases t with n | q
    · simp only [coins, QueryImpl.ofLift_eq_id'] at ih ⊢
      simp [costAdapterImpl_apply, ih]
    · simp [costAdapterImpl_apply, ResetPolicy.rerun_apply, simulateQ_map, StateT.run_map, ih]

/-- Forgetting the accumulated reported cost of an attempt of `costAdapter alg` against frozen
reruns gives the attempt of `alg` against the reruns' outputs. -/
theorem map_attempt_costAdapter_eq_attempt {Q α β : Type}
    (run : Q → OracleComp spec (α × ℕ)) (alg : OracleComp (unifSpec + rerunSpec Q α) β) :
    (fun z => (z.1.1, z.2)) <$> P.attempt run (costAdapter alg) =
      P.attempt (fun q => Prod.fst <$> run q) alg := by
  simp only [ResetPolicy.attempt, costAdapter, Functor.map_map,
    ← P.map_run_simulateQ_rerun_costAdapterImpl run alg 0 (P.empty, 0)]

/-- Forgetting the accumulated query cost of a charged attempt gives the attempt against the
uninstrumented reruns. -/
theorem map_chargedAttempt_eq_attempt {Q α β : Type}
    (run : Q → OracleComp spec α) (cm : CostModel spec ℕ)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) :
    (fun z => (z.1.1, z.2)) <$> P.chargedAttempt run cm alg = P.attempt run alg := by
  rw [chargedAttempt, map_attempt_costAdapter_eq_attempt]
  simp only [fst_map_runAdd_instrumentedRun]

private theorem le_of_mem_support_run_simulateQ_rerun_costAdapterImpl {Q α β : Type}
    (run : Q → OracleComp spec (α × ℕ)) (c : ℕ)
    (hc : ∀ q st, ∀ z ∈ support ((simulateQ P.answer (run q)).run st), z.1.2 ≤ c)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) (s : ℕ) (st : P.World × ℕ) :
    ∀ z ∈ support ((simulateQ (coins (S := P.World × ℕ) + P.rerun run)
          ((simulateQ costAdapterImpl alg).run s)).run st),
      z.1.2 + c * st.2 ≤ s + c * z.2.2 := by
  induction alg using OracleComp.inductionOn generalizing s st with
  | pure b => simp
  | query_bind t k ih =>
    rcases t with n | q
    · intro z hz
      obtain ⟨u, hz⟩ : ∃ u, z ∈ support ((simulateQ (coins (S := P.World × ℕ) + P.rerun run)
          ((simulateQ costAdapterImpl (k u)).run s)).run st) := by
        simpa [costAdapterImpl_apply, coins] using hz
      exact ih u s st z hz
    · intro z hz
      obtain ⟨a, d, w, cur, ha, hz⟩ : ∃ (a : α) (d : ℕ) (w : P.World) (cur : P.Cursor),
          ((a, d), (w, cur)) ∈ support ((simulateQ P.answer (run q)).run (st.1, P.begin)) ∧
            z ∈ support ((simulateQ (coins (S := P.World × ℕ) + P.rerun run)
              ((simulateQ costAdapterImpl (k a)).run (s + d))).run (w, st.2 + 1)) := by
        simpa [costAdapterImpl_apply, ResetPolicy.rerun_apply] using hz
      have hd : d ≤ c := hc q _ _ ha
      have hk := ih a (s + d) (w, st.2 + 1) z hz
      dsimp only at hk ⊢
      nlinarith

/-- If every complete run reports a cost at most `c` from every world and cursor, then on every
outcome of an attempt of `costAdapter alg` against frozen reruns the accumulated reported cost is
at most `c` times the number of complete runs. -/
theorem cost_le_mul_runs_of_mem_support_attempt_costAdapter {Q α β : Type}
    (run : Q → OracleComp spec (α × ℕ)) (c : ℕ)
    (hc : ∀ q st, ∀ z ∈ support ((simulateQ P.answer (run q)).run st), z.1.2 ≤ c)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) :
    ∀ z ∈ support (P.attempt run (costAdapter alg)), z.1.2 ≤ c * z.2 := by
  intro z hz
  rw [ResetPolicy.attempt, costAdapter, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  simpa using P.le_of_mem_support_run_simulateQ_rerun_costAdapterImpl run c hc alg 0 _ y hy

private theorem snd_le_of_mem_support_runAdd {α : Type} {oa : OracleComp spec α}
    {cm : CostModel spec ℕ} {c : ℕ} (hc : WorstCaseCostBound oa cm c) {z : α × ℕ}
    (hz : z ∈ support (instrumentedRun oa cm).runAdd) : z.2 ≤ c := by
  rw [AddWriterT.runAdd, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact (worstCaseCostBound_iff_support_bound _ _ _).1 hc y hy

/-- On every outcome of a charged attempt, the accumulated query cost is at most `c` times the
number of complete runs when every complete run of `run` has worst-case query cost at most `c`
under `cm`. -/
theorem cost_le_mul_runs_of_mem_support_chargedAttempt {Q α β : Type}
    (run : Q → OracleComp spec α) (cm : CostModel spec ℕ) (c : ℕ)
    (hc : ∀ q, WorstCaseCostBound (run q) cm c)
    (alg : OracleComp (unifSpec + rerunSpec Q α) β) :
    ∀ z ∈ support (P.chargedAttempt run cm alg), z.1.2 ≤ c * z.2 :=
  P.cost_le_mul_runs_of_mem_support_attempt_costAdapter _ c
    (fun q st _ hz => snd_le_of_mem_support_runAdd (hc q)
      (mem_support_of_mem_support_simulateQ_run _ _ st hz)) alg

private theorem fst_map_attempt_costAdapter_eq {Q α : Type} [Finite Q] {β : Type}
    (run : Q → OracleComp spec (α × ℕ)) (alg : OracleComp (unifSpec + rerunSpec Q α) β) :
    Prod.fst <$> P.attempt run (costAdapter alg) =ᵈ
      (do let g ← P.eagerTable run; runCharged alg (fun q => (g q).1) (fun q => (g q).2) 0) := by
  refine ((P.attempt_eagerTable run (costAdapter alg)).map _).trans ?_
  simp only [map_bind, fst_map_simulateQ_counted_costAdapter]
  exact EvalDistEq.rfl

/-- A finder of cost `T` against frozen reruns that report their own cost has expected accumulated
reported cost at most `T` times the expected largest reported cost of the eager table. -/
theorem expectedCalls_fst_attempt_costAdapter_le_lintegral_sup_mul [Fintype R] [DecidableEq R]
    [∀ r, Fintype (C r)] (run : ((r : R) → C r) → OracleComp spec (Bool × ℕ))
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) :
    expectedCalls (Prod.fst <$> P.attempt run (costAdapter find)) ≤
      (∫⁻ g, ((Finset.univ.sup fun q => (g q).2 : ℕ) : ℝ≥0∞) ∂𝒟[P.eagerTable run]) * T := by
  rw [expectedCalls_eq_of_evalDistEq (P.fst_map_attempt_costAdapter_eq run find)]
  exact h.expectedCalls_bind_runCharged_le_lintegral_sup_mul _ _ _

/-- A finder of cost `T` against frozen reruns that report a cost at most `c` on every outcome of
every honest complete run has expected accumulated reported cost at most `c * T`. -/
theorem expectedCalls_fst_attempt_costAdapter_le [Fintype R] [DecidableEq R]
    [∀ r, Fintype (C r)] (run : ((r : R) → C r) → OracleComp spec (Bool × ℕ))
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) (c : ℕ)
    (hc : ∀ q, ∀ z ∈ support (do (simulateQ impl (run q)).run' (← init)), z.2 ≤ c) :
    expectedCalls (Prod.fst <$> P.attempt run (costAdapter find)) ≤ c * T := by
  rw [expectedCalls_eq_of_evalDistEq (P.fst_map_attempt_costAdapter_eq run find)]
  refine h.expectedCalls_bind_runCharged_le (P.eagerTable run) (fun g q => (g q).1)
    (fun g q => (g q).2) c fun g hg q => hc q _ ?_
  rw [← support_eq_of_evalDistEq (P.eagerTable_marginal run q), support_map]
  exact ⟨g, hg, rfl⟩

/-- Against frozen reruns that return a verdict and a reported cost, one attempt of
`costAdapter find` satisfies the bounds of `Rewinding.ResetPolicy.finder_bounds` for the verdicts,
and its expected accumulated reported cost is at most `c * T` when every honest complete run
reports a cost at most `c`. -/
theorem finder_bounds_charged [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    (run : ((r : R) → C r) → OracleComp spec (Bool × ℕ))
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) (c : ℕ)
    (hc : ∀ q, ∀ z ∈ support (do (simulateQ impl (run q)).run' (← init)), z.2 ≤ c) :
    averageAcceptRate (P.eagerTable fun q => Prod.fst <$> run q) ≤
        κ + (1 - κ) * Pr{let z ← P.attempt run (costAdapter find)}[z.1.1.isSome] ∧
      expectedCalls ((fun z => (z.1.1, z.2)) <$> P.attempt run (costAdapter find)) ≤ T ∧
      expectedCalls (Prod.fst <$> P.attempt run (costAdapter find)) ≤ c * T := by
  have hb := P.finder_bounds (fun q => Prod.fst <$> run q) h
  rw [← P.map_attempt_costAdapter_eq_attempt run find, prEvent_map] at hb
  exact ⟨hb.1, hb.2, P.expectedCalls_fst_attempt_costAdapter_le run h c hc⟩

private theorem snd_le_of_mem_support_run'_runAdd {α : Type} {oa : OracleComp spec α}
    {cm : CostModel spec ℕ} {c : ℕ} (hc : WorstCaseCostBound oa cm c) :
    ∀ z ∈ support (do (simulateQ impl (instrumentedRun oa cm).runAdd).run' (← init)), z.2 ≤ c := by
  intro z hz
  obtain ⟨s, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  exact snd_le_of_mem_support_runAdd hc (support_simulateQ_run'_subset impl _ s hz)

/-- A finder of cost `T` charged by the query cost of `run` under `cm` has expected accumulated
query cost at most `c * T` when every complete run of `run` has worst-case query cost at most
`c`. -/
theorem expectedCalls_fst_chargedAttempt_le_of_worstCaseCostBound [Fintype R] [DecidableEq R]
    [∀ r, Fintype (C r)] (run : ((r : R) → C r) → OracleComp spec Bool)
    (cm : CostModel spec ℕ)
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) (c : ℕ) (hc : ∀ q, WorstCaseCostBound (run q) cm c) :
    expectedCalls (Prod.fst <$> P.chargedAttempt run cm find) ≤ c * T :=
  P.expectedCalls_fst_attempt_costAdapter_le _ h c fun q =>
    snd_le_of_mem_support_run'_runAdd (hc q)

/-- A finder of error `κ` and cost `T` against frozen reruns of `run` satisfies, in one charged
attempt, the success bound and complete-run bound `T` of `Rewinding.ResetPolicy.finder_bounds`,
and the expected query-cost bound `c * T` when every complete run of `run` has worst-case query
cost at most `c` under `cm`. -/
theorem finder_bounds_charged_of_worstCaseCostBound [Fintype R] [DecidableEq R]
    [∀ r, Fintype (C r)] (run : ((r : R) → C r) → OracleComp spec Bool)
    (cm : CostModel spec ℕ)
    {Out : Type} {good : (((r : R) → C r) → Bool) → Out → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option Out)} {κ T : ℝ≥0∞}
    (h : IsFinder good find κ T) (c : ℕ) (hc : ∀ q, WorstCaseCostBound (run q) cm c) :
    averageAcceptRate (P.eagerTable run) ≤
        κ + (1 - κ) * Pr{let z ← P.chargedAttempt run cm find}[z.1.1.isSome] ∧
      expectedCalls ((fun z => (z.1.1, z.2)) <$> P.chargedAttempt run cm find) ≤ T ∧
      expectedCalls (Prod.fst <$> P.chargedAttempt run cm find) ≤ c * T := by
  simpa only [fst_map_runAdd_instrumentedRun, chargedAttempt] using
    P.finder_bounds_charged _ h c fun q => snd_le_of_mem_support_run'_runAdd (hc q)

end ResetPolicy

end Rewinding
