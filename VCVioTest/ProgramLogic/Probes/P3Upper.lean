module

public import VCVio
public meta import VCVio.ProgramLogic.Tactics
public import Mathlib.Util.CountHeartbeats

-- A probe: its proofs are measurements, not library code, so Mathlib's style set is off.
set_option linter.mathlibStandardSet false

/-!
# Probe P3: the upper reading on current main, and a budgeted bad-event bound

* `Upper`: a port of `VCVio/ProgramLogic/Unary/WP/Upper.lean` from the reverted commit 49f365a74
  (instance, readback lemmas, pointwise and averaging rules). What changed on main:
  `predInd` is gone (`propInd` + `prEvent_eq_wp_propInd`); `wp⟦·⟧` is a scoped macro for the
  ambient `wp`, which clashes with `Std.WP.wp`, so the expectation is spelled
  `OracleComp.ProgramLogic.wp`; `SampleableType.wp_uniformSample_eq_sum` is gone
  (`OracleComp.Lower.wp_uniformSample_eq_tsum` + `tsum_fintype`); `ExpectationWP.wp_add` is
  `OracleComp.ProgramLogic.wp_add`; `wp_le_prEvent_add_of_support` is gone, so `Spec.bind_of_bad`
  is not ported; `SubSpec.PreservesAnswerMeasure` is gone, so the `liftComp` rules are not
  ported; the `upper_readback` simp set is gone (readback below is spelled out).
* The route classifier sends a bare `vcgen` on an upper triple to VCVio's `ℝ≥0∞` pipeline (the
  scoped instance's head is not in `Route.interpHeads`); `vcgen (errorOnMissingSpec := true)` or
  `vcgen [..]` reaches core `vcgen`.
* `sequential_old`: the P3 target, copied verbatim (baseline only, see the note there).
* `cacheHit_new`: a family member (`prEvent_cache_has_value_le_of_unique_preimage`) by a ranked
  invariant: potential `𝟙[bad] + k / C`, `simulateQ_triple_ranked`, and core `vcgen` through
  `cachingOracle`'s `get`/`match`/query/`modifyGet` for the one-step inequality.
-/

public section

universe u u'

open ENNReal Std.WP OrderDual OracleSpec OracleComp

namespace VCVioTest.ProgramLogic.Probes.P3Upper

namespace PL
export OracleComp.ProgramLogic (wp)
end PL

set_option experimental.vcgen true

/-! ## The upper reading, ported -/

namespace Upper

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec] {α : Type}

open scoped OracleComp.Lower in
/-- Core weakest preconditions of the expectation over the order duals. -/
noncomputable scoped instance (priority := 1300) instWP :
    Std.WP.WPMonad (OracleComp spec) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  ExactWPMonad.dual

open scoped OracleComp.Lower in
noncomputable scoped instance (priority := 1300) wpInst :
    Std.WP.WP (OracleComp spec α) α ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  (instWP (spec := spec)).toWP α

open scoped VCVioTest.ProgramLogic.Probes.P3Upper.Upper

theorem wp_eq (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    wp oa post epost = toDual (PL.wp oa fun a => ofDual (post a)) :=
  rfl

theorem ofDual_wp (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) (epost : EStack⟨⟩ᵒᵈ) :
    ofDual (wp oa post epost) = PL.wp oa fun a => ofDual (post a) :=
  rfl

theorem toDual_wp (oa : OracleComp spec α) (g : α → ℝ≥0∞) :
    toDual (PL.wp oa g) = wp oa (fun a => toDual (g a)) Lean.Order.bot :=
  rfl

theorem triple_iff (oa : OracleComp spec α) (pre : ℝ≥0∞ᵒᵈ) (post : α → ℝ≥0∞ᵒᵈ)
    (epost : EStack⟨⟩ᵒᵈ) :
    Triple oa pre post epost ↔ PL.wp oa (fun a => ofDual (post a)) ≤ ofDual pre :=
  Triple.iff

theorem wp_le_iff_triple (oa : OracleComp spec α) (g : α → ℝ≥0∞) (ε : ℝ≥0∞) :
    PL.wp oa g ≤ ε ↔ ⦃ toDual ε ⦄ oa ⦃ fun a => toDual (g a) ⦄ :=
  (triple_iff oa _ _ _).symm

open OracleComp.ProgramLogic in
theorem prEvent_le_iff_triple (oa : OracleComp spec α) (p : α → Prop) (ε : ℝ≥0∞) :
    Pr{let x ← oa}[p x] ≤ ε ↔ ⦃ toDual ε ⦄ oa ⦃ fun x => toDual (propInd (p x)) ⦄ := by
  rw [prEvent_eq_wp_propInd]
  exact (triple_iff oa _ _ _).symm

theorem rel_iff (a b : ℝ≥0∞ᵒᵈ) : Lean.Order.PartialOrder.rel a b ↔ ofDual b ≤ ofDual a :=
  Iff.rfl

theorem iInf_eq {κ : Type _} (f : κ → ℝ≥0∞ᵒᵈ) :
    Lean.Order.iInf f = toDual (⨆ i, ofDual (f i)) :=
  Lean.Order.PartialOrder.rel_antisymm
    (show (⨆ i, ofDual (f i)) ≤ ofDual (Lean.Order.iInf f) from
      iSup_le fun i => Lean.Order.iInf_le f i)
    (Lean.Order.le_iInf f _ fun i => le_iSup (fun i => ofDual (f i)) i)

theorem wp_le_iSup (oa : OracleComp spec α) (g : α → ℝ≥0∞) : PL.wp oa g ≤ ⨆ x, g x :=
  OracleComp.ProgramLogic.wp_le_const_of_support oa fun x _ => le_iSup g x

@[spec]
theorem Spec.monadLift_query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
      OracleComp spec (spec.Range t)) (Lean.Order.iInf post) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact wp_le_iSup _ _

@[spec]
theorem Spec.query (t : spec.Domain) (post : spec.Range t → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple (query t : OracleComp spec (spec.Range t)) (Lean.Order.iInf post) post epost := by
  rw [HasQuery.instOfMonadLift_query]
  exact Spec.monadLift_query t post

theorem Spec.ofSupport (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple oa (Lean.Order.iInf fun a : {a // a ∈ support oa} => post a.1) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact OracleComp.ProgramLogic.wp_le_const_of_support oa fun x hx =>
    le_iSup (fun a : {a // a ∈ support oa} => ofDual (post a.1)) ⟨x, hx⟩

theorem Spec.ofWp (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple oa (toDual (PL.wp oa fun a => ofDual (post a))) post epost := by
  rw [triple_iff, ofDual_toDual]

theorem triple_add_frame {oa : OracleComp spec α} {ε : ℝ≥0∞} {post : α → ℝ≥0∞ᵒᵈ} (c : ℝ≥0∞)
    (h : ⦃ toDual ε ⦄ oa ⦃ post ⦄) :
    ⦃ toDual (c + ε) ⦄ oa ⦃ fun a => toDual (c + ofDual (post a)) ⦄ := by
  rw [triple_iff] at h ⊢
  simp only [ofDual_toDual] at h ⊢
  rw [OracleComp.ProgramLogic.wp_add]
  exact add_le_add (OracleComp.ProgramLogic.wp_le_const_of_support oa fun _ _ => le_rfl) h

end Upper

namespace Upper

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec]

open scoped VCVioTest.ProgramLogic.Probes.P3Upper.Upper

@[spec]
theorem Spec.uniformSample (β : Type) [SampleableType β] (post : β → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} : Triple ($ᵗ β) (Lean.Order.iInf post) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact wp_le_iSup _ _

theorem Spec.uniformSample_avg (β : Type) [SampleableType β] [Fintype β] (post : β → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    Triple ($ᵗ β) (toDual ((∑ x, ofDual (post x)) / Fintype.card β)) post epost := by
  rw [triple_iff, ofDual_toDual, OracleComp.Lower.wp_uniformSample_eq_tsum, tsum_fintype,
    Nat.card_eq_fintype_card]

section Uniform

variable {ι : Type u} {spec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure spec]

/-- The exact rule for a query with uniform answers. -/
theorem Spec.query_avg (t : spec.Domain) [Fintype (spec.Range t)]
    (post : spec.Range t → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple (HasQuery.query t : OracleComp spec (spec.Range t))
      (toDual (∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * ofDual (post u))) post epost :=
  (triple_iff _ _ _ _).2 (OracleComp.ProgramLogic.wp_query_uniform t _).le

/-- `Spec.query_avg` for a lifted primitive query, the form `vcgen` reaches inside a handler. -/
theorem Spec.monadLift_query_avg (t : spec.Domain) [Fintype (spec.Range t)]
    (post : spec.Range t → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple (MonadLift.monadLift (liftM (OracleSpec.query t) : OracleQuery spec (spec.Range t)) :
        OracleComp spec (spec.Range t))
      (toDual (∑ u, (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ * ofDual (post u))) post epost :=
  (triple_iff _ _ _ _).2 (OracleComp.ProgramLogic.wp_query_uniform t _).le

end Uniform

end Upper

/-! ## Core `vcgen` over the dual carrier -/

section VCGen

open scoped VCVioTest.ProgramLogic.Probes.P3Upper.Upper
open OracleComp.ProgramLogic (propInd)
open Upper

/-- A bound that holds on every path: the pointwise (registered) rules. -/
example : ⦃ toDual 0 ⦄ (do let _ ← $ᵗ Bool; let c ← $ᵗ Bool; pure (c || true) : ProbComp Bool)
    ⦃ fun r => toDual (propInd (r = false)) ⦄ := by
  vcgen (errorOnMissingSpec := true)
  simp [propInd]

/-- A fractional bound: the averaging rule, applied explicitly. -/
example : ⦃ toDual 2⁻¹ ⦄ ($ᵗ Bool) ⦃ fun b => toDual (propInd (b = true)) ⦄ := by
  vcgen [Spec.uniformSample_avg]
  simp [propInd]

end VCGen

/-! ## The target, copied verbatim

Not re-proved. The proof is an induction over rounds whose step is the one-phase theorem
`prEvent_stablePhaseRunFrom_logged_le`, a custom bind rule: its continuation premise quantifies
over the terminal residual budget, cache bound, cache and log, under six invariants, and the
residual budget comes from `IsTotalQueryBound` of the proof-only accounting continuation, not
from the simulation state. Core `vcgen` cannot use such a rule as a spec: the potential after the
phase is not a function of the program state. The missing piece is a state-indexed form of the
phase theorem, with the residual budget carried in the state (a counter decremented per query,
say `StateT (QueryCache × ℕ)`), as an upper triple
`⦃ fun σ => toDual (N σ.2 (keys σ.1) / |Y|) ⦄ phaseRun ⦃ fun _ σ' => toDual (N σ'.2 (keys σ'.1) / |Y|) ⦄`
(plus the invariants as an assertion conjunct); the rounds would then compose as
`simulateQ_triple_ranked` does below. -/

section Sequential

open MerkleTreeMultiExtractability

variable {Cfg Query Address Y R C : Type}

#count_heartbeats in
theorem sequential_old
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y]
    [UniformAnswerMeasure (Query →ₒ Y)]
    (committer : SequentialCommitter Cfg Query Y)
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (finish : committer.State → ExtractorState Cfg Query Address Y config →
      OracleComp (Query →ₒ Y) R)
    (accountingFinish : committer.State → ExtractorState Cfg Query Address Y config →
      (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) C)
    (win : R → Prop)
    (nodeBudget checkpointCount verifierOverhead : ℕ)
    (perCheckpoint : ℕ)
    (hconfig : ∀ tag, config.nodeBudget tag ≤ perCheckpoint)
    (hfinish : ∀ privateState
        (state : ExtractorState Cfg Query Address Y config)
        (terminalRemaining terminalCached : ℕ)
        (cache : (Query →ₒ Y).QueryCache)
        (log : (Query →ₒ Y).QueryLog),
      IsTotalQueryBound (accountingFinish privateState state log) terminalRemaining →
      state.cumulativeLog = log →
      ¬ CacheHasCollision cache →
      (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
        ∀ input, cache input ≠ none → input ∈ keys) →
      (∀ entry ∈ log, cache entry.1 = some entry.2) →
      (∀ input value, cache input = some value →
        ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value) →
      state.StableAt view log →
      state.totalNodeBudget ≤ nodeBudget →
      state.checkpoints.length ≤ checkpointCount →
      Pr{let z ← (simulateQ (Query →ₒ Y).cachingOracle (finish privateState state)).run
             cache}[win z.1] ≤
        (multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
          terminalRemaining terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹)
    (rounds firstRound : ℕ) (privateState : committer.State)
    (extractorState : ExtractorState Cfg Query Address Y config)
    (cache : (Query →ₒ Y).QueryCache)
    (log : (Query →ₒ Y).QueryLog)
    (remaining cachedBound : ℕ)
    (hbound : IsTotalQueryBound
      (committer.runCommitmentsThenAccounting accountingFinish rounds firstRound privateState
        extractorState log) remaining)
    (hstateLog : extractorState.cumulativeLog = log)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query,
      keys.card ≤ cachedBound ∧
        ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : extractorState.StableAt view log)
    (hnodes : extractorState.totalNodeBudget + rounds * perCheckpoint ≤ nodeBudget)
    (hcheckpoints : extractorState.checkpoints.length + rounds ≤ checkpointCount) :
    Pr{let z ← (simulateQ (Query →ₒ Y).cachingOracle (committer.runCommitmentsThen rounds
           firstRound privateState extractorState finish)).run cache}[win z.1] ≤
      (multiCheckpointErrorNumerator nodeBudget checkpointCount verifierOverhead
        remaining cachedBound : ENNReal) *
          (Nat.card Y : ENNReal)⁻¹ := by
  induction rounds generalizing firstRound privateState extractorState cache log remaining
      cachedBound with
  | zero =>
      have hnodes0 : extractorState.totalNodeBudget ≤ nodeBudget := by simpa using hnodes
      have hcheckpoints0 : extractorState.checkpoints.length ≤ checkpointCount := by
        simpa using hcheckpoints
      have hterminal := hfinish privateState extractorState remaining cachedBound cache log
        (by simpa [SequentialCommitter.runCommitmentsThenAccounting] using hbound)
        hstateLog hno hcacheBound hlogCache hcacheLog hstable hnodes0 hcheckpoints0
      simpa [SequentialCommitter.runCommitmentsThen] using hterminal
  | succ rounds ih =>
      subst log
      unfold SequentialCommitter.runCommitmentsThen
      simp only [SequentialCommitter.runCommitments]
      rw [bind_assoc]
      change Pr{let z ← (simulateQ (Query →ₒ Y).cachingOracle ((committer.commit firstRound
                    privateState).withQueryLog >>= fun phaseResult => committer.runCommitmentsThen
                    rounds (firstRound + 1) phaseResult.1.2.2 (extractorState.record
                    phaseResult.1.1 phaseResult.2 phaseResult.1.2.1) finish)).run
                      cache}[win z.1] ≤ _
      rw [← adaptivePrefixRunFrom_commit_eq extractorState
        (committer.commit firstRound privateState)
        (fun output nextExtractorState =>
          committer.runCommitmentsThen rounds (firstRound + 1) output.2.2
            nextExtractorState finish) cache]
      apply prEvent_stablePhaseRunFrom_logged_le view extractorState
        (fun output currentLog =>
          committer.runCommitmentsThen rounds (firstRound + 1) output.2.2
            (extractorState.recordCumulative output.1 currentLog output.2.1) finish)
        (fun output currentLog =>
          committer.runCommitmentsThenAccounting accountingFinish rounds (firstRound + 1)
            output.2.2
            (extractorState.recordCumulative output.1 currentLog output.2.1) currentLog)
        win nodeBudget checkpointCount verifierOverhead
        (committer.commit firstRound privateState) remaining cachedBound
        extractorState.cumulativeLog
      · simpa only [SequentialCommitter.runCommitmentsThenAccounting] using hbound
      · exact hno
      · exact hcacheBound
      · exact hlogCache
      · exact hcacheLog
      · exact hstable
      · omega
      · omega
      · intro output terminalRemaining terminalCached terminalCache terminalLog
          hrest hno' hcacheBound' hlogCache' hcacheLog' hstable'
        obtain ⟨tag, root, nextPrivateState⟩ := output
        refine ih (firstRound := firstRound + 1) (privateState := nextPrivateState)
          (extractorState := extractorState.recordCumulative tag terminalLog root)
          (cache := terminalCache) (log := terminalLog)
          (remaining := terminalRemaining) (cachedBound := terminalCached)
          hrest (ExtractorState.recordCumulative_cumulativeLog _ _ _ _)
          hno' hcacheBound' hlogCache' hcacheLog'
          (hstable'.recordCumulative view tag terminalLog root) ?_ ?_
        · rw [ExtractorState.totalNodeBudget_recordCumulative]
          have htag := hconfig tag
          simp only [Nat.add_mul, one_mul] at hnodes
          omega
        · simp only [ExtractorState.recordCumulative_checkpoints, List.length_append,
            List.length_singleton]
          omega

end Sequential

/-! ## A budgeted bad-event bound through a ranked invariant -/

section Ranked

open OracleComp.ProgramLogic (propInd)

/-- **Ranked simulation** (`PolyFun`'s `triple_liftM_ranked_total`, restated for `simulateQ`; its
module `PolyFun.PFunctor.Free.WP.Charge` is not built here). -/
theorem simulateQ_triple_ranked {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    {n : Type → Type} [Monad n] {Pred EPred : Type} [Assertion Pred]
    [Assertion EPred] [WPMonad n Pred EPred] (handler : QueryImpl spec n) (Φ : ℕ → Pred)
    (E : EPred) (hstep : ∀ t k, Triple (handler t) (Φ (k + 1)) (fun _ => Φ k) E)
    (hdrop : ∀ k, Lean.Order.PartialOrder.rel (Φ k) (Φ 0))
    (oa : OracleComp spec α) (k : ℕ) (hx : IsTotalQueryBound oa k) :
    Triple (simulateQ handler oa) (Φ k) (fun _ => Φ 0) E := by
  induction oa using OracleComp.inductionOn generalizing k with
  | pure x => exact Triple.pure x (hdrop k)
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hx
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [simulateQ_query_bind]
    exact Triple.bind _ _ _ (hstep t j) fun u => ih u j (hx.2 u)

section CacheHit

open Finset
open scoped OracleSpec.PrimitiveQuery

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [UniformAnswerMeasure spec] [∀ t, Fintype (spec.Range t)]

#count_heartbeats in
/-- `OracleComp.prEvent_cache_has_value_le_of_unique_preimage`, copied verbatim. -/
theorem cacheHit_old {α : Type}
    [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (v₀ : spec.Range default)
    (cache₀ : QueryCache spec)
    (hunique_v₀ :
      ∀ t₀ t₁ : spec.Domain,
        ∀ v₁ : spec.Range t₀, ∀ v₂ : spec.Range t₁,
          cache₀ t₀ = some v₁ →
          cache₀ t₁ = some v₂ →
          HEq v₁ v₀ →
          HEq v₂ v₀ →
          t₀ = t₁) :
    Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ t₀ : spec.Domain,
        ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] ≤
      (n : ℝ≥0∞) * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  classical
  let C := (Fintype.card (spec.Range default) : ℝ≥0∞)
  induction oa using OracleComp.inductionOn generalizing n cache₀ with
  | pure x =>
    rw [simulateQ_pure]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h => ?_) bot_le
    change z ∈ support (pure (x, cache₀) : OracleComp _ _) at hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨t₀, v, hcache, hnone, _⟩ := h
    simp [hnone] at hcache
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at hbound
    obtain ⟨hpos, hrest⟩ := hbound
    by_cases ht : ∃ v, cache₀ t = some v
    · obtain ⟨v, hv⟩ := ht
      have hrun : (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
          (simulateQ cachingOracle (mx v)).run cache₀ := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        have hcache : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
            pure (v, cache₀) := by
          simp [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, hv, pure_bind, StateT.run_pure]
        rw [hcache, pure_bind]
        simp [OracleQuery.cont_query]
      rw [hrun]
      calc Pr{let z ← (simulateQ cachingOracle (mx v)).run cache₀}[∃ t₀ v,
            z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀]
          ≤ ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ := ih v (n - 1) (hrest v) cache₀ hunique_v₀
        _ ≤ (n : ℝ≥0∞) * C⁻¹ := by gcongr; exact_mod_cast Nat.sub_le n 1
    · push Not at ht
      have ht_none : cache₀ t = none := Option.eq_none_iff_forall_ne_some.mpr ht
      have hrun : (simulateQ cachingOracle (liftM (query t) >>= mx)).run cache₀ =
          (liftM (query t) >>= fun u =>
            (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)) := by
        simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
        have hstep : (liftM (cachingOracle t) : StateT _ (OracleComp spec) _).run cache₀ =
            (liftM (query t) >>= fun u =>
              pure (u, cache₀.cacheQuery t u) : OracleComp spec _) := by
          simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
            StateT.run_bind, StateT.run_get, pure_bind, ht_none]
          change (StateT.lift (PFunctor.FreeM.lift (P := spec.toPFunctor) t) cache₀ >>= _) = _
          simp only [StateT.lift, monad_norm,
            modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, StateT.run]
          rfl
        rw [hstep]; simp [monad_norm]
      rw [hrun]
      have hih : ∀ u ∈ support (liftM (query t) : OracleComp spec (spec.Range t)),
          ¬HEq u v₀ →
          Pr{let z ← (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)}[∃ t₀ v,
            z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] ≤
          ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ := by
        intro u _ heq_v₀
        have hunique_v₀' :
            ∀ t₀ t₁ : spec.Domain,
              ∀ v₁ : spec.Range t₀, ∀ v₂ : spec.Range t₁,
                (cache₀.cacheQuery t u) t₀ = some v₁ →
                (cache₀.cacheQuery t u) t₁ = some v₂ →
                HEq v₁ v₀ →
                HEq v₂ v₀ →
                t₀ = t₁ := by
          intro t₀ t₁ v₁ v₂ hcache₁ hcache₂ hheq₁ hheq₂
          by_cases heq_t₀ : t₀ = t
          · subst heq_t₀
            rw [QueryCache.cacheQuery_self] at hcache₁
            cases hcache₁
            exact (heq_v₀ hheq₁).elim
          · by_cases heq_t₁ : t₁ = t
            · subst heq_t₁
              rw [QueryCache.cacheQuery_self] at hcache₂
              cases hcache₂
              exact (heq_v₀ hheq₂).elim
            · rw [QueryCache.cacheQuery_of_ne _ _ heq_t₀] at hcache₁
              rw [QueryCache.cacheQuery_of_ne _ _ heq_t₁] at hcache₂
              exact hunique_v₀ t₀ t₁ v₁ v₂ hcache₁ hcache₂ hheq₁ hheq₂
        refine le_trans (prEvent_mono_of_support _ _ (fun z => ∃ t₀ v, z.2 t₀ = some v ∧
            (cache₀.cacheQuery t u) t₀ = none ∧ HEq v v₀)
          fun z hz ⟨t₀, v, hcache_f, hnone₀, hheq⟩ => ?_) (ih u (n - 1) (hrest u) _ hunique_v₀')
        by_cases heq_t : t₀ = t
        · exfalso
          subst heq_t
          have hle := simulateQ_cachingOracle_cache_le (mx u) (cache₀.cacheQuery t₀ u) _ hz
          have hzu : z.2 t₀ = some u := hle (QueryCache.cacheQuery_self cache₀ t₀ u)
          rw [hzu] at hcache_f; cases hcache_f
          exact heq_v₀ hheq
        · exact ⟨t₀, v, hcache_f,
            (QueryCache.cacheQuery_of_ne cache₀ u heq_t).trans hnone₀, hheq⟩
      have hhit : Pr{let u ← (liftM (query t) : OracleComp spec (spec.Range t))}[HEq u v₀] ≤
          C⁻¹ := by
        rw [prEvent_liftM_query_eq_card_div]
        have hcard : (Finset.univ.filter fun u : spec.Range t => HEq u v₀).card ≤ 1 :=
          Finset.card_le_one.mpr fun a ha b hb => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            exact eq_of_heq (ha.trans hb.symm)
        calc ((Finset.univ.filter fun u : spec.Range t => HEq u v₀).card : ℝ≥0∞) /
              Fintype.card (spec.Range t)
            ≤ 1 / Fintype.card (spec.Range t) := by gcongr; exact_mod_cast hcard
          _ ≤ C⁻¹ := by
            rw [one_div]; exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (hrange t))
      calc Pr{let z ← (liftM (query t) : OracleComp spec (spec.Range t)) >>= fun u =>
              (simulateQ cachingOracle (mx u)).run (cache₀.cacheQuery t u)}[∃ t₀ v,
                z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀]
          ≤ C⁻¹ + ((n - 1 : ℕ) : ℝ≥0∞) * C⁻¹ :=
            (prEvent_bind_le_prEvent_add_of_support _ _ (fun u => HEq u v₀) _ hih).trans
              (add_le_add hhit le_rfl)
        _ = (n : ℝ≥0∞) * C⁻¹ := by
            rw [← one_add_mul, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_cancel' hpos]


open scoped VCVioTest.ProgramLogic.Probes.P3Upper.Upper in
#count_heartbeats in
/-- The same bound by a ranked invariant: the potential is the bad event's indicator plus
`C⁻¹` per remaining query. No cache invariant is needed: the unique-preimage hypothesis is
unused (kept only so the statement matches). -/
theorem cacheHit_new {α : Type} [Inhabited ι]
    (oa : OracleComp spec α)
    (n : ℕ) (hbound : IsTotalQueryBound oa n)
    (hrange : ∀ t, Fintype.card (spec.Range default) ≤ Fintype.card (spec.Range t))
    (v₀ : spec.Range default)
    (cache₀ : QueryCache spec)
    (_hunique_v₀ :
      ∀ t₀ t₁ : spec.Domain,
        ∀ v₁ : spec.Range t₀, ∀ v₂ : spec.Range t₁,
          cache₀ t₀ = some v₁ →
          cache₀ t₁ = some v₂ →
          HEq v₁ v₀ →
          HEq v₂ v₀ →
          t₀ = t₁) :
    Pr{let z ← (simulateQ cachingOracle oa).run cache₀}[∃ t₀ : spec.Domain,
        ∃ v : spec.Range t₀, z.2 t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀] ≤
      (n : ℝ≥0∞) * (Fintype.card (spec.Range default) : ℝ≥0∞)⁻¹ := by
  classical
  set C := (Fintype.card (spec.Range default) : ℝ≥0∞)
  set bad : QueryCache spec → Prop := fun c => ∃ t₀ v, c t₀ = some v ∧ cache₀ t₀ = none ∧ HEq v v₀
  have himp : ∀ c t (x : spec.Range t), bad (c.cacheQuery t x) → bad c ∨ HEq x v₀ := by
    rintro c t x ⟨t₀, v, hv, hnone, hheq⟩
    by_cases ht : t₀ = t
    · subst ht; rw [QueryCache.cacheQuery_self] at hv; cases hv; exact .inr hheq
    · rw [QueryCache.cacheQuery_of_ne _ _ ht] at hv; exact .inl ⟨t₀, v, hv, hnone, hheq⟩
  have hstep : ∀ t k, ⦃ fun c => toDual (propInd (bad c) + (k + 1 : ℕ) * C⁻¹) ⦄
      (spec.cachingOracle t) ⦃ fun _ c => toDual (propInd (bad c) + k * C⁻¹) ⦄ := by
    intro t k
    vcgen [cachingOracle.apply_eq, Upper.Spec.query_avg, Upper.Spec.monadLift_query_avg]
    all_goals simp only [Upper.rel_iff, ofDual_toDual, binderNameHint, StateT.wp_apply_eq,
      StateT.run_modifyGet, Upper.ofDual_wp, OracleComp.ProgramLogic.wp_pure]
    · gcongr; simp
    · rename_i c _
      set c' := (Fintype.card (spec.Range t) : ℝ≥0∞)
      calc ∑ x, c'⁻¹ * (propInd (bad (c.cacheQuery t x)) + k * C⁻¹)
          ≤ ∑ x, (c'⁻¹ * (propInd (bad c) + k * C⁻¹) + c'⁻¹ * propInd (HEq x v₀)) := by
            gcongr with x
            rw [← mul_add, add_right_comm]
            gcongr
            exact (OracleComp.ProgramLogic.propInd_mono (himp c t x)).trans
              OracleComp.ProgramLogic.propInd_or_le
        _ ≤ (propInd (bad c) + k * C⁻¹) + C⁻¹ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              ← mul_assoc, ← Finset.mul_sum]
            gcongr
            · exact (mul_le_of_le_one_left' (ENNReal.mul_inv_le_one _))
            · simp only [OracleComp.ProgramLogic.propInd_eq_ite, Finset.sum_boole]
              have hcard : (Finset.univ.filter fun u : spec.Range t => HEq u v₀).card ≤ 1 :=
                Finset.card_le_one.mpr fun a ha b hb => by
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
                  exact eq_of_heq (ha.trans hb.symm)
              calc c'⁻¹ * _ ≤ c'⁻¹ * 1 := by gcongr; exact_mod_cast hcard
                _ ≤ C⁻¹ := by
                  rw [mul_one]; exact ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (hrange t))
        _ = propInd (bad c) + (k + 1 : ℕ) * C⁻¹ := by push_cast; ring
  have hrank := simulateQ_triple_ranked spec.cachingOracle
    (fun k c => toDual (propInd (bad c) + k * C⁻¹)) Lean.Order.bot (by simpa using hstep)
    (fun k c => by
      simp only [Upper.rel_iff, ofDual_toDual, Nat.cast_zero, zero_mul, add_zero]
      exact le_self_add) oa n hbound
  have h := hrank.le_wp cache₀
  simp only [StateT.wp_apply_eq, Upper.rel_iff, ofDual_toDual, Upper.ofDual_wp] at h
  have h0 : ¬bad cache₀ := fun ⟨_, _, hv, hn, _⟩ => by simp [hn] at hv
  rw [OracleComp.ProgramLogic.prEvent_eq_wp_propInd]
  simpa [OracleComp.ProgramLogic.propInd_eq_zero_iff.2 h0] using h

end CacheHit

end Ranked

end VCVioTest.ProgramLogic.Probes.P3Upper
