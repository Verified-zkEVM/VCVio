/-
Copyright (c) 2026 Lacramioara Astefanoaei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lacramioara Astefanoaei
-/

module

public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.MacAlg
public import VCVio.OracleComp.QueryTracking.LoggingOracle
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.SimSemantics.Append
public import ToMathlib.Control.StateT

/-!
# Deterministic MAC from a PRF

The standard construction of a message authentication code from a pseudorandom function
(Boneh-Shoup v0.6, §6.3; Katz-Lindell, Construction 4.3):

- `tag k m := pure (prf.eval k m)`
- `verify k m t := pure (t == prf.eval k m)`

## Main Definitions

- `PRFScheme.toMacAlg` — the derived MAC from a PRF.
- `PRFScheme.toMacAlg_perfectlyComplete` — honest tags always verify.

## Security (Boneh-Shoup Theorem 6.2)

- `PRFScheme.macToPRFReduction` — the PRF distinguisher constructed from a UF-CMA forger.
- `PRFScheme.strongUnforgeableAdvantage_toMacAlg_eq_unforgeableAdvantage` — for this deterministic
  MAC, strong (pair-fresh) and ordinary (message-fresh) unforgeability advantages coincide.
- `PRFScheme.prf_implies_suf_cma` — PRF security implies SUF-CMA security:
  `strongUnforgeableAdvantage(A) ≤ prfAdvantage(prf, B) + 1/|R|`.
- `PRFScheme.prf_implies_uf_cma` — PRF security implies UF-CMA security, with the same bound.

## References

- [Bellare, Namprempre, *Authenticated Encryption: Relations among Notions and Analysis of the
  Generic Composition Paradigm*, ASIACRYPT 2000](https://eprint.iacr.org/2000/025)
- [Boneh, Shoup, *A Graduate Course in Applied Cryptography*, v0.6, §6.3]
  (https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf)
-/

@[expose] public section

open MeasureTheory OracleComp OracleSpec ENNReal

namespace PRFScheme

variable {K D R : Type}

/-! ## Construction -/

/-- The deterministic MAC derived from a PRF: tagging is PRF evaluation,
verification recomputes and compares. -/
def toMacAlg [DecidableEq R] (prf : PRFScheme K D R) : MacAlg ProbComp D K R where
  keygen := prf.keygen
  tag k m := pure (prf.eval k m)
  verify k m t := pure (decide (t = prf.eval k m))

/-- The derived MAC is perfectly complete: an honestly generated tag always verifies. -/
theorem toMacAlg_perfectlyComplete [DecidableEq R] (prf : PRFScheme K D R) :
    prf.toMacAlg.PerfectlyComplete ProbCompRuntime.probComp := by
  intro msg
  let : MeasurableSpace K := ⊤
  rw [ProbCompRuntime.probComp_evalDist]
  simp only [toMacAlg, monad_norm, decide_true]
  rw [show (do let k ← prf.keygen; pure true) = (fun _ => true) <$> prf.keygen by
    simp only [map_eq_bind_pure_comp, Function.comp_def]]
  rw [evalDist_map_apply prf.keygen measurable_const (measurableSet_singleton true)]
  rw [show (fun _ : K => true) ⁻¹' {true} = Set.univ by ext; simp,
    OracleComp.evalDist_apply_univ_eq_one]

/-! ## Security Reduction (Boneh-Shoup Theorem 6.2)

Given a UF-CMA forger `A` against `prf.toMacAlg`, we construct a PRF distinguisher `B`
(`macToPRFReduction A`) and prove:

    strongUnforgeableAdvantage(A) ≤ prfAdvantage(prf, B) + 1/|R|

The reduction forwards `A`'s tagging queries to its own PRF/random-function oracle while
logging them, then checks the forgery condition.

**Strong vs ordinary UF-CMA.** Boneh-Shoup's Attack Game 6.1 checks that the forgery *pair*
`(m, t)` is fresh; this is `MacAlg.strongUnforgeableExp`. `MacAlg.unforgeableExp` checks only
message freshness (`!log.wasQueried msg`). For the deterministic MAC `prf.toMacAlg`, each
message has exactly one valid tag, so the two advantages coincide
(`strongUnforgeableAdvantage_toMacAlg_eq_unforgeableAdvantage`). The reduction is analysed in the
message-fresh game (`prf_implies_uf_cma`) and the bound transfers to the strong game
(`prf_implies_suf_cma`).
-/

/-- Query the `(D →ₒ R)` component of the PRF oracle spec. -/
def prfFuncQuery (msg : D) :
    OracleComp (unifSpec + (D →ₒ R)) R :=
  (unifSpec + (D →ₒ R)).query (Sum.inr msg)

/-- Oracle implementation for the reduction: forwards `unifSpec` queries transparently
and forwards `(D →ₒ R)` queries to the ambient oracle while logging them. -/
def macToPRFQueryImpl :
    QueryImpl (unifSpec + (D →ₒ R))
      (WriterT (QueryLog (D →ₒ R)) (OracleComp (unifSpec + (D →ₒ R)))) :=
  let fwdTag : QueryImpl (D →ₒ R) (OracleComp (unifSpec + (D →ₒ R))) :=
    fun msg => prfFuncQuery msg
  unifSpec.passthrough +
  fwdTag.withLogging

/-- Composing the outer `prfRealQueryImpl` with the inner `macToPRFQueryImpl` gives exactly
the forgery-game run `MacAlg.runWithTaggingOracle` (which uses `withLogging` over
`pure ∘ prf.eval k`). -/
private theorem simulateQ_prfReal_macToPRFQueryImpl_run [DecidableEq R]
    {α : Type} (prf : PRFScheme K D R) (k : K)
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) :
    simulateQ (prfRealQueryImpl prf k)
        ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) oa).run) =
      (prf.toMacAlg).runWithTaggingOracle k oa := by
  rw [MacAlg.runWithTaggingOracle_def, QueryImpl.simulateQ_writerTMapBase_run]
  congr 2
  funext t
  cases t with
  | inl n =>
      ext
      change (fun a => (a, ([] : QueryLog (D →ₒ R)))) <$>
          simulateQ (prfRealQueryImpl prf k)
            (OracleComp.liftComp
              (liftM (unifSpec.query n) : OracleComp unifSpec _)
              (unifSpec + (D →ₒ R))) =
        (fun a => (a, ([] : QueryLog (D →ₒ R)))) <$>
          (liftM (unifSpec.query n) : ProbComp _)
      rw [simulateQ_prfRealQueryImpl_liftComp]
  | inr d =>
      ext
      simp [QueryImpl.writerTMapBase, macToPRFQueryImpl, prfFuncQuery,
        toMacAlg, MacAlg.taggingOracle, map_eq_bind_pure_comp]

/-- In the real tagging game for `prf.toMacAlg`, every entry of the tagging log records the PRF
value at its message: the tagging oracle is deterministic. -/
private theorem snd_eq_eval_of_mem_log_runWithTaggingOracle [DecidableEq R] (prf : PRFScheme K D R)
    (k : K)
    {α : Type} (oa : OracleComp (unifSpec + (D →ₒ R)) α) {z : α × QueryLog (D →ₒ R)}
    (hz : z ∈ support ((prf.toMacAlg).runWithTaggingOracle k oa)) :
    ∀ e ∈ z.2, e.2 = prf.eval k e.1 := by
  induction oa using OracleComp.inductionOn generalizing z with
  | pure x =>
    simp only [MacAlg.runWithTaggingOracle_def, simulateQ_pure, WriterT.run_pure', support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    simp
  | query_bind t f ih =>
    cases t with
    | inl n =>
      rw [MacAlg.runWithTaggingOracle_def, QueryImpl.passthrough_add,
        QueryImpl.simulateQ_add_query_bind_left] at hz
      simp only [QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
        WriterT.run_bind', mem_support_bind_iff, support_map, Set.mem_image] at hz
      obtain ⟨⟨u, w⟩, hu, z', hz', rfl⟩ := hz
      simp only [WriterT.run_liftM, support_map, Set.mem_image, Prod.mk.injEq] at hu
      obtain ⟨_, _, _, rfl⟩ := hu
      intro e he
      exact ih u hz' e (by simpa using he)
    | inr d =>
      rw [MacAlg.runWithTaggingOracle_def, QueryImpl.passthrough_add,
        QueryImpl.simulateQ_add_query_bind_right] at hz
      simp only [WriterT.run_bind', mem_support_bind_iff, support_map, Set.mem_image] at hz
      obtain ⟨⟨u, w⟩, hu, z', hz', rfl⟩ := hz
      simp only [MacAlg.taggingOracle, toMacAlg, QueryImpl.withLogging_apply, bind_pure_comp,
        WriterT.run_bind, WriterT.run_liftM, List.empty_eq, map_pure, WriterT.run_map,
        WriterT.run_tell, List.nil_append, MonadAttach.support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      intro e he
      simp only [Prod.map_snd, List.singleton_append, List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · exact ih _ hz' e he

variable [DecidableEq D]

/-- The PRF distinguisher constructed from a UF-CMA forger. Runs the forger with
logged-and-forwarded oracles, then verifies the forgery via one additional oracle query.
If the forger makes Q tagging queries, the reduction makes Q + 1 oracle queries total;
this can be tracked separately via `IsTotalQueryBound`. -/
def macToPRFReduction [DecidableEq R] (prf : PRFScheme K D R)
    (adversary : (prf.toMacAlg).UnforgeableAdversary) :
    PRFAdversary D R :=
  ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) adversary.main).run >>=
    fun ((msg, τ), log) => prfFuncQuery msg >>= fun t =>
      pure (!QueryLog.wasQueried log msg && decide (τ = t)) :
    OracleComp (unifSpec + (D →ₒ R)) Bool)

/-- The prfRealExp with the reduction equals the UF-CMA body as a `ProbComp` computation. -/
private theorem prfRealExp_macToPRFReduction_eq_body [DecidableEq R] (prf : PRFScheme K D R)
    (adversary : (prf.toMacAlg).UnforgeableAdversary) :
    prf.prfRealExp (macToPRFReduction prf adversary) = (do
      let k ← prf.keygen
      let ((msg, τ), log) ← (prf.toMacAlg).runWithTaggingOracle k adversary.main
      pure (!QueryLog.wasQueried log msg && decide (τ = prf.eval k msg)) :
    ProbComp Bool) := by
  unfold prfRealExp macToPRFReduction
  refine bind_congr fun k => ?_
  rw [simulateQ_bind, simulateQ_prfReal_macToPRFQueryImpl_run prf k]
  refine bind_congr fun x => ?_
  erw [simulateQ_bind, simulateQ_prfRealQueryImpl_inr, pure_bind, simulateQ_pure]

/-- In the real PRF experiment, the reduction reproduces exactly the UF-CMA game. -/
theorem prfRealExp_macToPRFReduction_eq_unforgeableAdvantage [DecidableEq R]
    (prf : PRFScheme K D R) (adversary : (prf.toMacAlg).UnforgeableAdversary) :
    Pr[= true | prf.prfRealExp (macToPRFReduction prf adversary)] =
      MacAlg.unforgeableAdvantage ProbCompRuntime.probComp adversary := by
  rw [prfRealExp_macToPRFReduction_eq_body]
  rw [← evalDist_apply_singleton]
  unfold MacAlg.unforgeableAdvantage MacAlg.unforgeableExp
  rw [ProbCompRuntime.probComp_evalDist]
  rfl

/-- The ideal experiment decomposes as: run the forger (under the random-oracle simulation
producing a log and cache), then perform one final random-oracle query and check the forgery.

This is the ideal-world analogue of `prfRealExp_macToPRFReduction_eq_body`. -/
private theorem prfIdealExp_macToPRFReduction_eq_ideal_body [DecidableEq R] [SampleableType R]
    (prf : PRFScheme K D R)
    (adversary : (prf.toMacAlg).UnforgeableAdversary) :
    prfIdealExp (macToPRFReduction prf adversary) =
      ((simulateQ prfIdealQueryImpl
        ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) adversary.main).run)).run ∅ >>=
      fun (((msg, τ), log), cache) =>
        ((D →ₒ R).randomOracle msg).run cache >>= fun (t, _) =>
          (pure (!QueryLog.wasQueried log msg && decide (τ = t)) : ProbComp Bool)) := by
  unfold prfIdealExp macToPRFReduction
  rw [simulateQ_bind]
  simp only [StateT.run'_bind']
  refine bind_congr fun ⟨⟨⟨msg, τ⟩, log⟩, cache⟩ => ?_
  rw [simulateQ_bind]
  simp only [prfFuncQuery]
  erw [simulateQ_prfIdealQueryImpl_inr]
  simp

/-- Inductive step of `log_cache_invariant_aux` for a `unifSpec` query: the uniform
query never touches the `(D →ₒ R)` cache, so the invariant is inherited from the
continuation via the inductive hypothesis `ih`. -/
private theorem log_cache_invariant_step_unif [SampleableType R]
    {α : Type} (msg : D) (cache₀ : (D →ₒ R).QueryCache)
    (z : (α × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache) (hcache : z.2 msg ≠ none)
    (n : ℕ) (f : (unifSpec + (D →ₒ R)).Range (Sum.inl n) → OracleComp (unifSpec + (D →ₒ R)) α)
    (ih : ∀ (u : (unifSpec + (D →ₒ R)).Range (Sum.inl n)) (cache₀ : (D →ₒ R).QueryCache),
      ∀ z ∈ support
        ((simulateQ prfIdealQueryImpl (simulateQ macToPRFQueryImpl (f u)).run).run cache₀),
        z.2 msg ≠ none → cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true)
    (hmem : z ∈ support ((simulateQ prfIdealQueryImpl
      (simulateQ macToPRFQueryImpl (liftM (OracleSpec.query (Sum.inl n)) >>= f)).run).run cache₀)) :
    cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true := by
  rw [macToPRFQueryImpl, QueryImpl.passthrough_add, QueryImpl.simulateQ_add_query_bind_left]
    at hmem
  simp only [QueryImpl.liftTarget_apply, QueryImpl.id'_apply,
    WriterT.run_bind', simulateQ_bind, StateT.run_bind] at hmem
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨⟨⟨val, log_q⟩, cache_mid⟩, hu, hmem⟩ := hmem
  change ((val, log_q), cache_mid) ∈ support
    ((simulateQ prfIdealQueryImpl
      ((fun u => (u, ([] : QueryLog (D →ₒ R)))) <$>
        OracleComp.liftComp
          (liftM (unifSpec.query n) : OracleComp unifSpec _)
          (unifSpec + (D →ₒ R)))).run cache₀) at hu
  rw [simulateQ_map, simulateQ_prfIdealQueryImpl_liftComp] at hu
  simp only [StateT.run_map, StateT.run_monadLift, support_map] at hu
  obtain ⟨u, hu, hvalue⟩ := hu
  have hlog : log_q = ([] : QueryLog (D →ₒ R)) :=
    (congrArg (fun x => x.1.2) hvalue).symm
  have hmem' : z ∈ support ((simulateQ prfIdealQueryImpl
      (simulateQ macToPRFQueryImpl (f val)).run).run cache_mid) := by
    simpa only [hlog, List.nil_append, macToPRFQueryImpl, QueryImpl.passthrough_add, show
        (Prod.map (@id α) fun x : QueryLog (D →ₒ R) => x) = id from
          funext fun ⟨_, _⟩ => rfl, id_map] using hmem
  simp only [support_bind, Set.mem_iUnion, exists_prop,
    support_pure, Set.mem_singleton_iff] at hu
  obtain ⟨answer, _, hu_eq⟩ := hu
  rcases ih val cache_mid z hmem' hcache with hcache' | hlog'
  · left
    have hcache_eq : cache₀ = cache_mid :=
      (congrArg Prod.snd hu_eq).symm.trans (congrArg Prod.snd hvalue)
    rwa [hcache_eq]
  · exact Or.inr hlog'

/-- Inductive step of `log_cache_invariant_aux` for a `(D →ₒ R)` query: forwarding the
query through `macToPRFQueryImpl` logs `msg'`. If the tracked point `msg` equals `msg'`
it is now in the log; otherwise the query leaves `cache_mid msg` unchanged and the
invariant is inherited from the continuation via the inductive hypothesis `ih`. -/
private theorem log_cache_invariant_step_query [SampleableType R]
    {α : Type} (msg : D) (cache₀ : (D →ₒ R).QueryCache)
    (z : (α × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache) (hcache : z.2 msg ≠ none)
    (msg' : D) (f : (unifSpec + (D →ₒ R)).Range (Sum.inr msg') → OracleComp (unifSpec + (D →ₒ R)) α)
    (ih : ∀ (u : (unifSpec + (D →ₒ R)).Range (Sum.inr msg')) (cache₀ : (D →ₒ R).QueryCache),
      ∀ z ∈ support
        ((simulateQ prfIdealQueryImpl (simulateQ macToPRFQueryImpl (f u)).run).run cache₀),
        z.2 msg ≠ none → cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true)
    (hmem : z ∈ support ((simulateQ prfIdealQueryImpl (simulateQ macToPRFQueryImpl
      (liftM (OracleSpec.query (Sum.inr msg')) >>= f)).run).run cache₀)) :
    cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true := by
  rw [macToPRFQueryImpl, QueryImpl.passthrough_add, QueryImpl.simulateQ_add_query_bind_right]
    at hmem
  simp only [prfFuncQuery, WriterT.run_bind', simulateQ_bind, StateT.run_bind] at hmem
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨⟨⟨val, log_q⟩, cache_mid⟩, hro, hmem⟩ := hmem
  dsimp only [Prod.fst, Prod.snd] at hmem
  rw [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hmem
  obtain ⟨⟨⟨res, inner_log⟩, inner_cache⟩, hinner, rfl⟩ := hmem
  simp only [Prod.map, id]
  erw [QueryImpl.run_withLogging_apply] at hro
  erw [simulateQ_bind] at hro
  by_cases heq : msg = msg'
  · subst heq; right
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hro
    obtain ⟨⟨_, _⟩, _, ⟨⟨rfl, rfl⟩, _⟩⟩ := hro
    exact QueryLog.wasQueried_cons_self
  · simp only [StateT.run_bind] at hro
    erw [simulateQ_prfIdealQueryImpl_inr] at hro
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hro
    obtain ⟨⟨q_val, q_cache⟩, hro_q, hmem2⟩ := hro
    dsimp only at hmem2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hmem2
    rw [randomOracle.apply_eq] at hro_q
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hro_q
    have hcache_mid_eq : cache_mid msg = cache₀ msg := by
      rcases hc : cache₀ msg' with _ | u₀
      · simp only [hc, StateT.run_bind, StateT.run_monadLift, StateT.run_modifyGet,
          support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at hro_q
        obtain ⟨i, ⟨_, _, hi⟩, _, hcm⟩ := hro_q
        subst hi; dsimp only [Prod.fst, Prod.snd] at hcm
        rw [hcm]
        simp [heq]
      · simp only [hc, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hro_q
        rw [hro_q.2]
    rcases ih val cache_mid ((res, inner_log), inner_cache) hinner hcache with hinv | hinv
    · left; rwa [hcache_mid_eq] at hinv
    · right
      simp only [List.singleton_append] at *
      rw [QueryLog.wasQueried_cons_of_ne (Ne.symm heq)]
      exact hinv

/-- Generalized log-cache invariant for arbitrary initial cache. Every domain point
cached in the final state was either already cached initially, or was logged. -/
private theorem log_cache_invariant_aux [SampleableType R]
    {α : Type}
    (oa : OracleComp (unifSpec + (D →ₒ R)) α)
    (cache₀ : (D →ₒ R).QueryCache)
    (z : (α × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache)
    (hmem : z ∈ support
      ((simulateQ prfIdealQueryImpl
        ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) oa).run)).run cache₀))
    (msg : D) (hcache : z.2 msg ≠ none) :
    cache₀ msg ≠ none ∨ QueryLog.wasQueried z.1.2 msg = true := by
  induction oa using OracleComp.inductionOn generalizing cache₀ z with
  | pure x =>
    simp only [simulateQ_pure, WriterT.run_pure'] at hmem
    subst hmem; exact Or.inl hcache
  | query_bind t f ih =>
    cases t with
    | inl n => exact log_cache_invariant_step_unif msg cache₀ z hcache n f ih hmem
    | inr msg' => exact log_cache_invariant_step_query msg cache₀ z hcache msg' f ih hmem

/-- **Log-cache invariant**: every domain point cached by the random oracle was
also logged by `macToPRFQueryImpl`. This holds because `macToPRFQueryImpl` logs
every `(D →ₒ R)` query as part of forwarding it, and forwarding is the only path
that populates the cache. -/
private theorem log_cache_invariant [SampleableType R]
    (adversary_main : OracleComp (unifSpec + (D →ₒ R)) (D × R))
    (state : (((D × R) × QueryLog (D →ₒ R)) × (D →ₒ R).QueryCache))
    (hmem : state ∈ support
      ((simulateQ prfIdealQueryImpl
        ((simulateQ (macToPRFQueryImpl (D := D) (R := R)) adversary_main).run)).run ∅))
    (msg : D) (hcache : state.2 msg ≠ none) :
    QueryLog.wasQueried state.1.2 msg = true := by
  simpa [QueryCache.empty_apply] using
    log_cache_invariant_aux adversary_main ∅ state hmem msg hcache

/-- In the ideal PRF experiment (random oracle), the reduction outputs `true` with probability
at most `1/|R|`. A fresh random-oracle query on `msg` returns a uniform `t ← $ᵗ R` independent of
the forger's claimed tag `τ`, so `Pr[τ = t] = 1/|R|`; if `msg` was already queried the output is
`false`. -/
theorem prfIdealExp_macToPRFReduction_le [DecidableEq R] [SampleableType R]
    [Fintype R]
    (prf : PRFScheme K D R) (adversary : (prf.toMacAlg).UnforgeableAdversary) :
    Pr[= true | prfIdealExp (macToPRFReduction prf adversary)] ≤
      (Fintype.card R : ℝ≥0∞)⁻¹ := by
  rw [prfIdealExp_macToPRFReduction_eq_ideal_body, probOutput_bind_eq_expectedValue]
  refine OracleComp.EvalDist.expectedValue_le_of_support fun ⟨((msg, τ), log), cache⟩ hmem => ?_
  dsimp only
  cases hcache : cache msg with
  | some v =>
    simp only [randomOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind, hcache,
      StateT.run_pure, log_cache_invariant adversary.main (((msg, τ), log), cache) hmem msg
        (by change cache msg ≠ none; rw [hcache]; exact Option.some_ne_none _),
      probOutput_pure]
    exact zero_le
  | none =>
    rw [show ((D →ₒ R).randomOracle msg).run cache =
        (fun u => (u, cache.cacheQuery msg u)) <$> ($ᵗ R) from
      QueryImpl.withCaching_run_none _ hcache]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp, pure_bind]
    rw [probOutput_bind_eq_tsum]
    simp only [probOutput_uniformSample, probOutput_pure, mul_ite, mul_one, mul_zero]
    set c := (Fintype.card R : ℝ≥0∞)⁻¹
    calc ∑' t, (if (true : Bool) = (!log.wasQueried msg && decide (τ = t)) then c else 0)
        ≤ ∑' t, (if t = τ then c else 0) :=
          ENNReal.tsum_le_tsum fun t => by
            split_ifs with h1 h2
            · exact le_rfl
            · simp only [Bool.true_eq, Bool.and_eq_true, decide_eq_true_eq] at h1
              exact absurd h1.2.symm h2
            all_goals exact zero_le
      _ = c := tsum_ite_eq τ (fun _ => c)

/-- **Boneh-Shoup Theorem 6.2.** PRF security implies UF-CMA security for the derived MAC:
for any forger `A`, the constructed distinguisher `macToPRFReduction prf A` satisfies
`unforgeableAdvantage(A) ≤ prfAdvantage(prf, B) + 1/|R|`. -/
theorem prf_implies_uf_cma [DecidableEq R] [SampleableType R] [Fintype R]
    (prf : PRFScheme K D R) (adversary : (prf.toMacAlg).UnforgeableAdversary) :
    MacAlg.unforgeableAdvantage ProbCompRuntime.probComp adversary ≤
      prf.prfAdvantage (macToPRFReduction prf adversary) + (Fintype.card R : ℝ≥0∞)⁻¹ := by
  rw [← prfRealExp_macToPRFReduction_eq_unforgeableAdvantage prf adversary,
    ← evalDist_apply_singleton, prfAdvantage, add_comm]
  refine (MeasureTheory.Measure.apply_true_le_add_boolDist _
    𝒟[prfIdealExp (macToPRFReduction prf adversary)]).trans ?_
  gcongr
  rw [evalDist_apply_singleton]
  exact prfIdealExp_macToPRFReduction_le prf adversary

/-! ## Strong Unforgeability

For the deterministic MAC `prf.toMacAlg`, a verifying pair `(msg, τ)` has `τ = prf.eval k msg`,
which is exactly the entry the tagging oracle logs when queried on `msg`. A verifying pair is
therefore fresh iff its message is, so the SUF-CMA and UF-CMA advantages coincide and Boneh-Shoup
Theorem 6.2 holds for strong unforgeability with the same reduction and bound.
-/

/-- In the real tagging game for `prf.toMacAlg`, the tagging log contains the pair
`(msg, prf.eval k msg)` exactly when `msg` was queried. -/
private theorem taggingLogContains_eval_eq_wasQueried [DecidableEq R] (prf : PRFScheme K D R)
    (k : K) (msg : D) (log : QueryLog (D →ₒ R))
    (hlog : ∀ e ∈ log, e.2 = prf.eval k e.1) :
    MacAlg.taggingLogContains log msg (prf.eval k msg) = log.wasQueried msg := by
  cases hw : log.wasQueried msg with
  | false =>
    cases hc : MacAlg.taggingLogContains log msg (prf.eval k msg)
    · rfl
    · rw [MacAlg.wasQueried_eq_true_of_taggingLogContains_eq_true _ _ _ hc] at hw
      exact absurd hw Bool.noConfusion
  | true =>
    rw [QueryLog.wasQueried_eq_decide_mem_map_fst, decide_eq_true_eq, List.mem_map] at hw
    obtain ⟨⟨m, t⟩, he, rfl⟩ := hw
    have ht : t = prf.eval k m := hlog _ he
    subst ht
    simpa [MacAlg.taggingLogContains] using he

/-- For the deterministic MAC `prf.toMacAlg`, strong and ordinary unforgeability coincide: the only
valid tag on a message is its PRF value, which is the tag the oracle returns on that message, so a
verifying pair is in the tagging log iff its message was queried. -/
theorem strongUnforgeableAdvantage_toMacAlg_eq_unforgeableAdvantage [DecidableEq R]
    (prf : PRFScheme K D R) (adversary : (prf.toMacAlg).UnforgeableAdversary) :
    MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adversary =
      MacAlg.unforgeableAdvantage ProbCompRuntime.probComp adversary := by
  unfold MacAlg.strongUnforgeableAdvantage MacAlg.strongUnforgeableExp MacAlg.unforgeableAdvantage
    MacAlg.unforgeableExp
  rw [ProbCompRuntime.probComp_evalDist, ProbCompRuntime.probComp_evalDist]
  congr 1
  refine evalDist_bind_congr _ _ _ fun k => ?_
  refine evalDist_bind_congr_of_support _ _ _ fun ⟨⟨msg, τ⟩, log⟩ hmem => ?_
  have hlog := snd_eq_eval_of_mem_log_runWithTaggingOracle prf k adversary.main hmem
  simp only [toMacAlg, pure_bind]
  by_cases hτ : τ = prf.eval k msg
  · subst hτ
    rw [taggingLogContains_eval_eq_wasQueried prf k msg log hlog]
  · simp [hτ]

/-- **Boneh-Shoup Theorem 6.2**, strong form. PRF security implies SUF-CMA security for the
derived MAC, with the pair-freshness forgery condition of Bellare-Namprempre (2000) and Boneh-Shoup
Attack Game 6.1: for any forger `A`, the constructed distinguisher `macToPRFReduction prf A`
satisfies `strongUnforgeableAdvantage(A) ≤ prfAdvantage(prf, B) + 1/|R|`. -/
theorem prf_implies_suf_cma [DecidableEq R] [SampleableType R] [Fintype R]
    (prf : PRFScheme K D R) (adversary : (prf.toMacAlg).UnforgeableAdversary) :
    MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adversary ≤
      prf.prfAdvantage (macToPRFReduction prf adversary) + (Fintype.card R : ℝ≥0∞)⁻¹ := by
  rw [strongUnforgeableAdvantage_toMacAlg_eq_unforgeableAdvantage]
  exact prf_implies_uf_cma prf adversary

end PRFScheme
