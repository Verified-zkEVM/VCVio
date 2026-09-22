/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SkgPrfHop
import all HashSig.SLHDSA.Security.SkgPrfHop

/-!
# The fresh-answer engine at the ideal secret-value experiment

`HashSig.SLHDSA.Security.SkgPrfHop` leaves the advantage `skgPrfIdealAdvantage` — the
`SKG_PRF` distinguisher's success probability in the ideal `PRF` experiment — and identifies the
*handler* that experiment runs under (`prfIdeal_mapStateTBase_skgLaneImpl`: one private-sampling
summand in front of `OracleSpec.nestedRandomOracle` of the public hash and the challenge
function).  It does not identify the *experiment*, so the fresh-answer engine of
`VCVio.OracleComp.QueryTracking.RandomOracle.Joint` was not applicable to it.  This module
supplies that identification and transports the engine across it.

`prfIdealExp_skgPrfReductionGen` rewrites `PRFScheme.prfIdealExp (skgPrfReductionGen core adv)` as
an equality of computations: the two seed samples pulled out in front, then the nested lazy run of
the provider-parametric game `romGameCoreGen` from the two empty caches, which is `skgIdealRun`.
`skgPrfIdealAdvantage_eq` reads the surviving advantage off the cache-carrying experiment
`skgIdealExpFull`, and `evalDist_skgIdealRun_setOf_le` transports
`OracleComp.evalDist_run_run_nested_setOf_le_of_fresh_bound` to it, so a predicate of the *joint*
cache — hash entries and secret entries together, glued by `OracleSpec.QueryCache.addEquiv` — that
fails at the empty cache and whose fresh-answer mass is at most `ε` holds of a run of at most `q`
joint entries with mass at most `q * ε`.

The twin of this module in the real lane is `HashSig.SLHDSA.Security.RomFresh`, which transports
the single-oracle engine to `romRunFull`.  The two differ in what they discharge: `RomFresh`
discharges the engine's cache-size side condition from `HasHashQueryBound`, and so leaves a bound
with no side condition; here the size conjunct stays *inside* the event, because no query bound on
the joint cache exists (see the scope below).

## The demonstration, and what it is not

`SecretHitsTarget` and `evalDist_skgIdealExpFull_wins_and_secretHitsTarget_le` are a
**demonstration** that the chain composed here closes to a number of the shape *query budget over
node-type cardinality*, `q / Nat.card core.Y`.  They are not the campaign's hidden-value event and
are not a step towards bounding `skgPrfIdealAdvantage`: the event names a value `y₀` fixed in
advance of the experiment, which is what makes its fresh-answer mass small and what a real bad
event does not do.  Their purpose is to exhibit an end-to-end instantiation of the engine in this
lane, hypothesis-free, so that the shape of the surviving obligation is visible.

The corresponding *negative* result is deliberately not library content:
`HashSigTest.SLHDSA.SkgIdealFresh` exhibits a joint-cache over-approximation of the hidden-value
event whose fresh-answer mass is one, and records why no cache-only predicate can do better.

## Scope

* **The ideal advantage is not bounded here.**  Every bound below is on the mass of a
  *restricted* event — winning, and a joint-cache predicate, and at most `q` joint entries — with
  the predicate and its fresh-answer bound supplied by the caller.  Nothing here bounds
  `skgPrfIdealAdvantage` itself, and no bound on it follows from this module alone.  What changed
  is that the engine is now **applicable** to this experiment; the surviving term remains an
  assumption slot.
* **Two implications are missing, and neither is discharged anywhere in the repository.**
  * A random-oracle bridge in the *ideal* lane, sending a winning run to a bad event of the joint
    cache.  The landed bridge (`HashSig.SLHDSA.Security.RomBridge`) is stated over `romRunFull`
    and over the public-hash cache alone; and by the refutation recorded in
    `HashSigTest.SLHDSA.SkgIdealFresh`, its hidden-value disjunct cannot be a joint-cache
    predicate at all, so the bridge cannot simply be restated over the joint cache.
  * A lane-independent query bound on the *joint* cache, counting hash and secret entries
    together.  `HasHashQueryBound` is real-lane-only and hash-only,
    `SLHDSA.Security.enncard_le_of_hasHashQueryBound` has no ideal analogue, and the secret-query
    accounting is stated nowhere.  Until it exists, the size conjunct
    `QueryCache.enncard … ≤ q` cannot be discharged and stays inside the event.
* The measurable-space instance on the outcome type is pinned to `⊤` by a `letI` inside each
  statement, inherited from the engine.  Pinning `⊤` is lossless wherever
  `DiscreteMeasurableSpace` holds, since that instance makes every set measurable and so equals
  `⊤`.  A consumer must fix `⊤` as well.
* Secret-value queries are still not counted anywhere; `q` here is a bound on the joint cache
  supplied inside the event, not a budget derived from an adversary.
* Nothing here is quantum: both oracles are classically lazily-sampled tables and the engine's
  step count is a classical query count.

## Labels

Twelve declarations.  There is no private declaration and no instance.

*The ideal experiment's run*:

* `SLHDSA.Security.run'_simulateQ_prfIdeal_liftComp_bind`, `SLHDSA.Security.skgIdealRun`,
  `SLHDSA.Security.prfIdealExp_skgPrfReductionGen`, `SLHDSA.Security.skgIdealExpFull`,
  `SLHDSA.Security.skgPrfIdealAdvantage_eq`.

*The engine transported*:

* `SLHDSA.Security.evalDist_skgIdealRun_setOf_le`,
  `SLHDSA.Security.evalDist_skgIdealExpFull_setOf_le`,
  `SLHDSA.Security.evalDist_skgIdealExpFull_wins_and_setOf_le`.

*The demonstration*:

* `SLHDSA.Security.SecretHitsTarget`, `SLHDSA.Security.not_secretHitsTarget_empty`,
  `SLHDSA.Security.evalDist_secretHitsTarget_fresh_le`,
  `SLHDSA.Security.evalDist_skgIdealExpFull_wins_and_secretHitsTarget_le`.

## References

- NIST FIPS 205, §9, Algorithms 18--19
- `VCVio.OracleComp.QueryTracking.RandomOracle.Joint` for the nested-oracle fresh-answer engine
  `OracleComp.evalDist_run_run_nested_setOf_le_of_fresh_bound`
- `HashSig.SLHDSA.Security.RomFresh` for the same transport in the real lane
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec ENNReal SignatureAlg MeasureTheory

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
  [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]

/-- The oracle family the whole experiment runs in: private sampling together with the public
hash. -/
local notation "romSpec" => unifSpec + publicHashSpec core

/-! ## The ideal experiment's run -/

omit [SampleableType core.SkSeed] [SampleableType (Bytes vp.params.m)] [DecidableEq core.AdrsKey]
  [DecidableEq core.Y] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- The ideal `PRF` handler is transparent on a lifted private computation at the head of a
program, so the sample commutes out of the run. -/
theorem run'_simulateQ_prfIdeal_liftComp_bind {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp (PRFScheme.PRFOracleSpec (core.PkSeed × Adrs) core.Y) β)
    (c : ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) :
    (simulateQ (PRFScheme.prfIdealQueryImpl (D := core.PkSeed × Adrs) (R := core.Y))
        (OracleComp.liftComp oa _ >>= k)).run' c =
      oa >>= fun x => (simulateQ (PRFScheme.prfIdealQueryImpl
        (D := core.PkSeed × Adrs) (R := core.Y)) (k x)).run' c := by
  rw [simulateQ_bind, PRFScheme.simulateQ_prfIdealQueryImpl_liftComp, StateT.run'_eq,
    StateT.run_bind, StateT.run_monadLift]
  simp [StateT.run'_eq]

/-- The ideal experiment's run at fixed seeds: the provider-parametric game interpreted by the
private-sampling summand in front of the two nested lazy oracles, from both empty caches, keeping
both caches. -/
noncomputable def skgIdealRun
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    (skPrf : core.SkPrf) (pkSeed : core.PkSeed) :
    ProbComp ((Bool × PublicHash.Cache core) ×
      ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) :=
  (((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (PublicHash.Cache core)
          (StateT ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache ProbComp)) +
      OracleSpec.nestedRandomOracle (publicHashSpec core) ((core.PkSeed × Adrs) →ₒ core.Y))
      (romGameCoreGen core adv skPrf pkSeed)).run ∅).run ∅)

/-- **The ideal `PRF` experiment at the `SKG_PRF` reduction, as a run of the nested handler.**
The two seed samples come out in front and the rest is the win bit of `skgIdealRun`. -/
theorem prfIdealExp_skgPrfReductionGen
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    PRFScheme.prfIdealExp (skgPrfReductionGen core adv) =
      (do
        let skPrf ← ($ᵗ core.SkPrf : ProbComp core.SkPrf)
        let pkSeed ← ($ᵗ core.PkSeed : ProbComp core.PkSeed)
        (fun w => w.1.1) <$> skgIdealRun core adv skPrf pkSeed) := by
  rw [PRFScheme.prfIdealExp, skgPrfReductionGen, run'_simulateQ_prfIdeal_liftComp_bind]
  refine bind_congr fun skPrf => ?_
  rw [run'_simulateQ_prfIdeal_liftComp_bind]
  refine bind_congr fun pkSeed => ?_
  rw [QueryImpl.simulateQ_mapStateTBase_run', prfIdeal_mapStateTBase_skgLaneImpl, skgIdealRun]
  simp [StateT.run'_eq, Functor.map_map]

/-- The cache-carrying ideal experiment: the two seed samples, then the nested lazy run of the
provider-parametric game from the two empty caches. -/
noncomputable def skgIdealExpFull
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    ProbComp ((Bool × PublicHash.Cache core) ×
      ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) :=
  (do
    let skPrf ← ($ᵗ core.SkPrf : ProbComp core.SkPrf)
    let pkSeed ← ($ᵗ core.PkSeed : ProbComp core.PkSeed)
    skgIdealRun core adv skPrf pkSeed)

/-- **The advantage surviving the `SKG_PRF` hop is the win-bit mass of the cache-carrying ideal
experiment.**  This is what makes a statement about `skgIdealExpFull` a statement about
`skgPrfIdealAdvantage`. -/
theorem skgPrfIdealAdvantage_eq
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    (letI : MeasurableSpace ((Bool × PublicHash.Cache core) ×
        ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) := ⊤;
      skgPrfIdealAdvantage core adv = 𝒟[skgIdealExpFull core adv] {z | z.1.1 = true}) := by
  let _ : MeasurableSpace ((Bool × PublicHash.Cache core) ×
      ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) := ⊤
  rw [skgPrfIdealAdvantage, prfIdealExp_skgPrfReductionGen, skgIdealExpFull]
  rw [show (do
      let skPrf ← ($ᵗ core.SkPrf : ProbComp core.SkPrf)
      let pkSeed ← ($ᵗ core.PkSeed : ProbComp core.PkSeed)
      ((fun w => w.1.1) <$> skgIdealRun core adv skPrf pkSeed) : ProbComp Bool) =
      (fun w => w.1.1) <$> (do
        let skPrf ← ($ᵗ core.SkPrf : ProbComp core.SkPrf)
        let pkSeed ← ($ᵗ core.PkSeed : ProbComp core.PkSeed)
        skgIdealRun core adv skPrf pkSeed) from by
    simp [map_eq_bind_pure_comp, bind_assoc]]
  rw [evalDist_map_of_discrete, MeasureTheory.Measure.map_apply Measurable.of_discrete
    MeasurableSet.of_discrete]
  rfl

/-! ## The engine transported -/

/-- **The fresh-answer bound, at the ideal experiment's run.**  For a predicate of the joint
cache that fails at the empty cache and whose fresh-answer mass is at most `ε`, the mass of the
runs whose joint cache satisfies it and has at most `q` entries is at most `q * ε`. -/
theorem evalDist_skgIdealRun_setOf_le
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    (skPrf : core.SkPrf) (pkSeed : core.PkSeed)
    (P : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).QueryCache → Prop)
    (hP : ¬ P ∅) (ε : ℝ≥0∞) (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Domain)
      (c : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).QueryCache), ¬ P c →
      c t = none →
      (letI : MeasurableSpace
          ((publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Range t) := ⊤;
        𝒟[($ᵗ (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Range t :
            ProbComp _)] {u | P (c.cacheQuery t u)} ≤ ε))
    (q : ℕ) :
    (letI : MeasurableSpace ((Bool × PublicHash.Cache core) ×
        ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) := ⊤;
      𝒟[skgIdealRun core adv skPrf pkSeed]
        {z | P (OracleSpec.QueryCache.addEquiv _ _ (z.1.2, z.2)) ∧
          OracleSpec.QueryCache.enncard
            (OracleSpec.QueryCache.addEquiv _ _ (z.1.2, z.2)) ≤ (q : ℝ≥0∞)} ≤
        (q : ℝ≥0∞) * ε) :=
  OracleComp.evalDist_run_run_nested_setOf_le_of_fresh_bound P hP ε hε hfresh
    (romGameCoreGen core adv skPrf pkSeed) q

/-- The same bound for the whole cache-carrying ideal experiment: the seed samples are uniform in
the bound, so they integrate out. -/
theorem evalDist_skgIdealExpFull_setOf_le
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    (P : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).QueryCache → Prop)
    (hP : ¬ P ∅) (ε : ℝ≥0∞) (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Domain)
      (c : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).QueryCache), ¬ P c →
      c t = none →
      (letI : MeasurableSpace
          ((publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Range t) := ⊤;
        𝒟[($ᵗ (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Range t :
            ProbComp _)] {u | P (c.cacheQuery t u)} ≤ ε))
    (q : ℕ) :
    (letI : MeasurableSpace ((Bool × PublicHash.Cache core) ×
        ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) := ⊤;
      𝒟[skgIdealExpFull core adv]
        {z | P (OracleSpec.QueryCache.addEquiv _ _ (z.1.2, z.2)) ∧
          OracleSpec.QueryCache.enncard
            (OracleSpec.QueryCache.addEquiv _ _ (z.1.2, z.2)) ≤ (q : ℝ≥0∞)} ≤
        (q : ℝ≥0∞) * ε) := by
  let _ : MeasurableSpace ((Bool × PublicHash.Cache core) ×
      ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) := ⊤
  let _ : MeasurableSpace core.SkPrf := ⊤
  let _ : MeasurableSpace core.PkSeed := ⊤
  rw [skgIdealExpFull]
  refine evalDist_bind_apply_le_of_forall _ _ MeasurableSet.of_discrete fun skPrf => ?_
  refine evalDist_bind_apply_le_of_forall _ _ MeasurableSet.of_discrete fun pkSeed => ?_
  exact evalDist_skgIdealRun_setOf_le core adv skPrf pkSeed P hP ε hε hfresh q

/-- **The ideal advantage restricted to a joint-cache event.**  The mass of the ideal
experiment's winning runs whose joint cache satisfies `P` and has at most `q` entries is at most
`q * ε`. -/
theorem evalDist_skgIdealExpFull_wins_and_setOf_le
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    (P : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).QueryCache → Prop)
    (hP : ¬ P ∅) (ε : ℝ≥0∞) (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Domain)
      (c : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).QueryCache), ¬ P c →
      c t = none →
      (letI : MeasurableSpace
          ((publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Range t) := ⊤;
        𝒟[($ᵗ (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Range t :
            ProbComp _)] {u | P (c.cacheQuery t u)} ≤ ε))
    (q : ℕ) :
    (letI : MeasurableSpace ((Bool × PublicHash.Cache core) ×
        ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) := ⊤;
      𝒟[skgIdealExpFull core adv]
        {z | z.1.1 = true ∧ P (OracleSpec.QueryCache.addEquiv _ _ (z.1.2, z.2)) ∧
          OracleSpec.QueryCache.enncard
            (OracleSpec.QueryCache.addEquiv _ _ (z.1.2, z.2)) ≤ (q : ℝ≥0∞)} ≤
        (q : ℝ≥0∞) * ε) := by
  let _ : MeasurableSpace ((Bool × PublicHash.Cache core) ×
      ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) := ⊤
  refine le_trans (MeasureTheory.measure_mono ?_)
    (evalDist_skgIdealExpFull_setOf_le core adv P hP ε hε hfresh q)
  exact fun _ hz => hz.2

/-! ## A demonstration: a secret value named in advance -/

/-- A value of the node type named in advance of the experiment is settled somewhere in the
challenge cache.  A *demonstration* predicate for the transported engine, not a bad event of the
run: `y₀` is a parameter, fixed before any sampling. -/
def SecretHitsTarget (y₀ : core.Y)
    (c : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).QueryCache) : Prop :=
  ∃ d : core.PkSeed × Adrs, c (Sum.inr d) = some y₀

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
  [SampleableType (Bytes vp.params.m)] [SampleableType core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.Y] in
/-- The empty cache settles no secret value, so it does not hit the named one. -/
theorem not_secretHitsTarget_empty (y₀ : core.Y) : ¬ SecretHitsTarget core y₀ ∅ := by
  simp [SecretHitsTarget]

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- **The fresh-answer mass of the named-value event is at most `1 / |Y|`.**  Only a challenge
query can turn it on, and only by drawing `y₀` itself; a public-hash answer cannot, because the
event reads the challenge half of the joint cache alone. -/
theorem evalDist_secretHitsTarget_fresh_le (y₀ : core.Y)
    (t : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Domain)
    (c : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).QueryCache)
    (hc : ¬ SecretHitsTarget core y₀ c) (ht : c t = none) :
    (letI : MeasurableSpace
        ((publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Range t) := ⊤;
      𝒟[($ᵗ (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Range t : ProbComp _)]
        {u | SecretHitsTarget core y₀ (c.cacheQuery t u)} ≤ (Nat.card core.Y : ℝ≥0∞)⁻¹) := by
  cases t with
  | inl t' =>
      let _ : MeasurableSpace ((publicHashSpec core).Range t') := ⊤
      rw [show {u : (publicHashSpec core + ((core.PkSeed × Adrs) →ₒ core.Y)).Range (Sum.inl t') |
          SecretHitsTarget core y₀ (c.cacheQuery (Sum.inl t') u)} = ∅ from by
        ext u
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨d, hd⟩
        rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ (by simp)] at hd
        exact hc ⟨d, hd⟩]
      simp
  | inr d =>
      let _ : MeasurableSpace core.Y := ⊤
      change 𝒟[($ᵗ core.Y : ProbComp core.Y)]
          {u : core.Y | SecretHitsTarget core y₀ (c.cacheQuery (Sum.inr d) u)} ≤ _
      have hsub : {u : core.Y | SecretHitsTarget core y₀ (c.cacheQuery (Sum.inr d) u)} ⊆
          ({y₀} : Set core.Y) := by
        rintro u ⟨d', hd'⟩
        rcases eq_or_ne d' d with rfl | hne
        · rw [OracleSpec.QueryCache.cacheQuery_self] at hd'
          exact Set.mem_singleton_iff.2 (Option.some.inj hd')
        · rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ (by simpa using hne)] at hd'
          exact absurd ⟨d', hd'⟩ hc
      refine le_trans (MeasureTheory.measure_mono hsub) ?_
      refine le_trans (SampleableType.evalDist_uniformSample_le_encard_div ({y₀} : Set core.Y)) ?_
      simp only [Set.encard_singleton]
      norm_num

open scoped Classical in
/-- **The demonstration closes to a number of the shape `q / |Y|`.**  The mass of the ideal
experiment's winning runs whose joint cache has at most `q` entries and settles the value named in
advance is at most `q / Nat.card core.Y`, with no hypothesis.

This is a demonstration that the chain of this module reaches a bound of the form *query budget
over node-type cardinality*.  It is not a bound on `skgPrfIdealAdvantage`: `y₀` is named before
the experiment, and the restriction to at most `q` joint entries is part of the event. -/
theorem evalDist_skgIdealExpFull_wins_and_secretHitsTarget_le
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    (y₀ : core.Y) (q : ℕ) :
    (letI : MeasurableSpace ((Bool × PublicHash.Cache core) ×
        ((core.PkSeed × Adrs) →ₒ core.Y).QueryCache) := ⊤;
      𝒟[skgIdealExpFull core adv]
        {z | z.1.1 = true ∧
          SecretHitsTarget core y₀ (OracleSpec.QueryCache.addEquiv _ _ (z.1.2, z.2)) ∧
          OracleSpec.QueryCache.enncard
            (OracleSpec.QueryCache.addEquiv _ _ (z.1.2, z.2)) ≤ (q : ℝ≥0∞)} ≤
        (q : ℝ≥0∞) / Nat.card core.Y) := by
  rw [ENNReal.div_eq_inv_mul, mul_comm]
  exact evalDist_skgIdealExpFull_wins_and_setOf_le core adv (SecretHitsTarget core y₀)
    (not_secretHitsTarget_empty core y₀) (Nat.card core.Y : ℝ≥0∞)⁻¹
    (by simpa using Nat.card_pos.ne')
    (fun t c hc ht => evalDist_secretHitsTarget_fresh_le core y₀ t c hc ht) q

end SLHDSA.Security
