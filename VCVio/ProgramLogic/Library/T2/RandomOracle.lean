/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.ProgramLogic.Library.T2.Caching
public import VCVio.ProgramLogic.Library.T2.Combinators

/-!
# Specifications for the lazy random oracle

Specifications for `randomOracle` (`uniformSampleImpl.withCaching`, over `ProbComp`) and the
random oracle model handler `romImpl = unifFwdImpl hashSpec + randomOracle`, under the necessary
reading of `ProbComp` (`open scoped OracleComp.Necessary`), together with the lazy-sampling
distribution facts.

* *One query.* `randomOracle_wp` (`spec high`) is the monotone frame, `randomOracle_wp_cacheQuery`
  the exact rule; `unifFwdImpl_wp` (`spec high`) reads a forwarded uniform query.
* *Whole runs.* `randomOracle` is `QueryImpl.MonotoneState` for the cache order through
  `QueryImpl.monotoneState_withCaching`, and so is the forwarding handler `unifFwdImpl`
  (`monotoneState_unifFwdImpl`), so the sum `romImpl` inherits the instance and T1's frame
  `Spec.simulateQ_monotoneState` steps over an opaque random-oracle-model adversary.
* *Lazy sampling.* On a hit `randomOracle` returns the stored answer (`run_of_eq_some`); on a miss
  its answer is a fresh uniform sample (`run'_of_eq_none`), so each answer at a fresh point has
  probability `1 / |R|` (`prEvent_run'_eq_of_eq_none`). With T1's
  `prEvent_run_eq_one_iff_triple`, the necessary-reading rules prove consistency facts such as
  "two queries at the same point agree with probability one".
-/

@[expose] public section

open OracleSpec OracleComp Std.WP ENNReal

open scoped OracleComp.Necessary

namespace randomOracle

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- On a hit, the random oracle returns the stored answer and keeps the cache. -/
@[simulateQ_nf]
theorem run_of_eq_some {t : spec.Domain} {c : spec.QueryCache} {u : spec.Range t}
    (h : c t = some u) : (spec.randomOracle t).run c = pure (u, c) :=
  QueryImpl.withCaching_run_some _ h

/-- On a miss, the random oracle samples a fresh uniform answer and caches it. -/
@[simulateQ_nf]
theorem run_of_eq_none {t : spec.Domain} {c : spec.QueryCache} (h : c t = none) :
    (spec.randomOracle t).run c = (fun u => (u, c.cacheQuery t u)) <$> ($ᵗ spec.Range t) :=
  QueryImpl.withCaching_run_none _ h

/-- On a hit, the answer of the random oracle is the stored one. -/
@[simulateQ_nf]
theorem run'_of_eq_some {t : spec.Domain} {c : spec.QueryCache} {u : spec.Range t}
    (h : c t = some u) : (spec.randomOracle t).run' c = pure u :=
  QueryImpl.withCaching_run'_of_eq_some _ h

/-- On a miss, the answer of the random oracle is a fresh uniform sample. -/
@[simulateQ_nf]
theorem run'_of_eq_none {t : spec.Domain} {c : spec.QueryCache} (h : c t = none) :
    (spec.randomOracle t).run' c = $ᵗ spec.Range t :=
  QueryImpl.withCaching_run'_of_eq_none _ h

/-- A reachable random-oracle step is a hit returning the stored answer, or a miss caching an
arbitrary answer. -/
@[simulateQ_nf high]
theorem mem_support_run_iff {t : spec.Domain} {c c' : spec.QueryCache} {v : spec.Range t} :
    (v, c') ∈ support ((spec.randomOracle t).run c) ↔
      (c t = some v ∧ c' = c) ∨ (c t = none ∧ c' = c.cacheQuery t v) := by
  rw [QueryImpl.mem_support_withCaching_run_iff, uniformSampleImpl_apply]
  simp

/-- At a fresh point, each answer of the random oracle has probability `1 / |R|`. -/
theorem prEvent_run'_eq_of_eq_none {t : spec.Domain} [Fintype (spec.Range t)]
    {c : spec.QueryCache} (h : c t = none) (u : spec.Range t) :
    Pr{let v ← (spec.randomOracle t).run' c}[v = u] = (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  rw [run'_of_eq_none h, SampleableType.prEvent_uniformSample_eq_singleton]

/-- At a fresh point, an event of the random oracle's answer has its uniform probability. -/
theorem prEvent_run'_of_eq_none {t : spec.Domain} {c : spec.QueryCache} (h : c t = none)
    (p : spec.Range t → Prop) :
    Pr{let v ← (spec.randomOracle t).run' c}[p v] = Pr{let v ← $ᵗ spec.Range t}[p v] := by
  rw [run'_of_eq_none h]

/-- At a cached point, an event of the random oracle's answer is decided by the stored answer. -/
theorem prEvent_run'_of_eq_some {t : spec.Domain} {c : spec.QueryCache} {u : spec.Range t}
    (h : c t = some u) (p : spec.Range t → Prop) [Decidable (p u)] :
    Pr{let v ← (spec.randomOracle t).run' c}[p v] = if p u then 1 else 0 := by
  rw [run'_of_eq_some h, prEvent_pure]

end randomOracle

namespace OracleComp.ProgramLogic

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- One random-oracle query in monotone-frame form: the final cache extends the initial one and
stores the answer. The default rule of `vcgen` for `randomOracle`. -/
@[spec high]
theorem randomOracle_wp (t : spec.Domain) (post : spec.Range t → spec.QueryCache → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v c', c ≤ c' → c' t = some v → post v c' ⦄
      (spec.randomOracle t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun c h v c' hz =>
    h v c' (QueryImpl.withCaching_cache_le _ t c _ hz) (QueryImpl.withCaching_run_caches _ t c _ hz)

/-- One random-oracle query, exactly: the answer is the stored one on a hit, and the final cache
is the initial one with the answer cached. -/
theorem randomOracle_wp_cacheQuery (t : spec.Domain)
    (post : spec.Range t → spec.QueryCache → Prop) {epost : EStack⟨⟩} :
    ⦃ fun c => ∀ v, (c t = none ∨ c t = some v) → post v (c.cacheQuery t v) ⦄
      (spec.randomOracle t) ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun c h v c' hz => by
    rcases randomOracle.mem_support_run_iff.1 hz with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
    · simpa [QueryCache.cacheQuery_eq_self_of_eq_some hc] using h v (Or.inr hc)
    · exact h v (Or.inl hc)

end OracleComp.ProgramLogic

/-! ## The random oracle model -/

namespace OracleComp.ProgramLogic

variable {ι : Type} {hashSpec : OracleSpec.{0, 0} ι}

/-- A forwarded uniform query samples and keeps the cache. -/
@[simulateQ_nf]
theorem unifFwdImpl_run_apply (n : ℕ) (s : hashSpec.QueryCache) :
    (unifFwdImpl hashSpec n).run s = (·, s) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  rw [unifFwdImpl, QueryImpl.liftTarget_apply, OracleComp.liftM_run_StateT,
    map_eq_bind_pure_comp]
  rfl

/-- A reachable forwarded uniform query keeps the cache. -/
theorem unifFwdImpl_run_snd_eq {n : ℕ} {s : hashSpec.QueryCache} {z : Fin (n + 1) × _}
    (hz : z ∈ support ((unifFwdImpl hashSpec n).run s)) : z.2 = s := by
  rw [unifFwdImpl_run_apply, support_map] at hz
  obtain ⟨u, -, rfl⟩ := hz
  rfl

/-- A forwarded uniform query may return any answer and keeps the cache. -/
@[spec high]
theorem unifFwdImpl_wp (n : ℕ) (post : Fin (n + 1) → hashSpec.QueryCache → Prop)
    {epost : EStack⟨⟩} :
    ⦃ fun s => ∀ u, post u s ⦄ unifFwdImpl hashSpec n ⦃ post; epost ⦄ :=
  (triple_stateT_iff_forall_mem_support _ _ _ _).2 fun s h u s' hz => by
    obtain rfl : s' = s := unifFwdImpl_run_snd_eq hz
    exact h u

/-- The forwarding handler keeps the cache, so it is monotone for the cache order and the random
oracle model handler `unifFwdImpl hashSpec + randomOracle` inherits the frame. -/
instance monotoneState_unifFwdImpl :
    (unifFwdImpl hashSpec).MonotoneState (· ≤ ·) :=
  .of_le fun _ _ _ hz => (unifFwdImpl_run_snd_eq hz).ge

end OracleComp.ProgramLogic
