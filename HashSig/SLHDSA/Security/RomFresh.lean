/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomRun
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
import all HashSig.SLHDSA.Security.CountedRom

/-!
# The fresh-answer bound for the SLH-DSA counted random-oracle run

`VCVio`'s `OracleComp.evalDist_run_setOf_le_of_fresh_bound` bounds by `q * ε` the mass of the
paths of a shared lazy random-oracle run whose final cache satisfies a predicate `P` that a
fresh answer makes fire with mass at most `ε`, *provided* the final cache has at most `q`
entries.  This module discharges that side condition for the SLH-DSA run of
`HashSig.SLHDSA.Security.RomRun`: `countedRomImpl_eq` identifies the counted interpretation with
the cost-instrumented shared lazy oracle, `mem_support_countedRomExperiment_of_mem_support_runAdd`
sends a path of the instrumented run to a path of `countedRomExperiment`, and
`enncard_le_of_hasHashQueryBound` concludes that under `HasHashQueryBound core adv q` every path
of `romRunFull` leaves a cache of at most `q` entries.  The consumable statement is
`evalDist_romRunFull_setOf_le_of_fresh_bound`: a cache predicate with fresh-answer mass at most
`ε` holds of the final cache of `romRunFull` with mass at most `q * ε`, with no side condition
left.

## Scope

* No bad event is defined here and nothing is said about which predicates have a small
  fresh-answer mass.  `P` is arbitrary; the caller supplies `hP` and `hfresh`.
* The budget `q` counts the public-hash queries of the *whole* experiment, including key
  generation, signing and the final verification, because `HasHashQueryBound` does.
* The bound is on the mass of `{z | P z.2}` under `romRunFull`, not on `romForgeAdvantage`.
  Relating a bad event of the final cache to the winning event is the job of the bridge, not of
  this module.
* The measurable-space instance on the outcome type is pinned to `⊤` by a `letI` inside the
  statement, inherited from the generic theorem.  Pinning `⊤` is lossless wherever
  `DiscreteMeasurableSpace` holds, since that instance makes every set measurable and so equals
  `⊤`; the statement is therefore the one a `[MeasurableSpace] [DiscreteMeasurableSpace]`
  formulation would give, and strictly stronger in general.  A consumer must fix `⊤` as well, and
  rewriting a set equality under the resulting `𝒟[…]` needs `simp [h]` rather than `rw [h]`.
* Nothing here is quantum: `PublicHash.randomOracle` is a classical lazily-sampled table and the
  budget is a classical query count.

## Labels

Four declarations.

*The fresh-answer bound for the counted run*:

* `SLHDSA.Security.countedRomImpl_eq`,
  `SLHDSA.Security.mem_support_countedRomExperiment_of_mem_support_runAdd`,
  `SLHDSA.Security.enncard_le_of_hasHashQueryBound`,
  `SLHDSA.Security.evalDist_romRunFull_setOf_le_of_fresh_bound`.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec MeasureTheory SignatureAlg
open scoped ENNReal

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
  [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)]

/-- The oracle family the whole experiment runs in: private sampling together with the public
hash. -/
local notation "romSpec" => unifSpec + publicHashSpec core

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
open scoped Classical in
/-- The counted interpretation is the shared lazy public-hash oracle instrumented with a charge
of `1` per public-hash query and `0` per private sample.  The body of `countedRomImpl` is not
exposed, so this is what identifies it with the generic instrumented run. -/
theorem countedRomImpl_eq :
    countedRomImpl core =
      (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core).withAddCost
        (fun q => match q with | .inl _ => 0 | .inr _ => 1) := by
  rfl

open scoped Classical in
/-- The winning bit and the charge of a path of the instrumented run are a path of the counted
experiment. -/
theorem mem_support_countedRomExperiment_of_mem_support_runAdd
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    {w : (RomOutcome vp core × ℕ) × PublicHash.Cache core}
    (hw : w ∈ support ((simulateQ (countedRomImpl core)
      (romGameCoreFull core adv)).runAdd.run ∅)) :
    (w.1.1.wins, w.1.2) ∈ support (countedRomExperiment core adv) := by
  rw [countedRomExperiment, romGameCore_eq_map, simulateQ_map, AddWriterT.runAdd_map,
    StateT.run'_eq, StateT.run_map, support_map, support_map]
  exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

open scoped Classical in
/-- **The query budget bounds the size of the final cache.**  Under a public-hash query budget
`q`, every path of `romRunFull` leaves a cache of at most `q` entries.  The charge counts every
query invocation, cached repeats and honest-party evaluations included, so the budget is at least
the number of distinct cached queries and the bound is sound but loose. -/
theorem enncard_le_of_hasHashQueryBound
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (q : ℕ)
    (hq : HasHashQueryBound core adv q)
    {z : RomOutcome vp core × PublicHash.Cache core} (hz : z ∈ support (romRunFull core adv)) :
    QueryCache.enncard z.2 ≤ (q : ℝ≥0∞) := by
  rw [romRunFull] at hz
  obtain ⟨n, hn⟩ := exists_mem_support_runAdd_of_mem_support_run _
    (fun q => match q with | .inl _ => 0 | .inr _ => 1) _ ∅ hz
  refine (enncard_le_add_cost_of_mem_support_runAdd_run_withAddCost _ (fun _ => le_rfl) _ ∅ _
    hn).trans ?_
  have hn2 : n ≤ q := hq _ (mem_support_countedRomExperiment_of_mem_support_runAdd core adv
    (by rw [countedRomImpl_eq]; exact hn))
  simp only [QueryCache.enncard_empty, zero_add]
  exact_mod_cast hn2

open scoped Classical in
/-- **The fresh-answer bound for the SLH-DSA counted random-oracle run.**  A cache predicate that
fails of the empty cache and whose fresh-answer firing mass is at most `ε` at every query and
every not-yet-firing cache holds of the final cache of the run with mass at most `q * ε`, where
`q` is the public-hash query budget of the whole experiment.

The measurable-space instance on the outcome type is pinned to `⊤` inside the statement, so a
consumer must fix `⊤` too. -/
theorem evalDist_romRunFull_setOf_le_of_fresh_bound
    (P : PublicHash.Cache core → Prop) (hP : ¬ P ∅) (ε : ℝ≥0∞) (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : (publicHashSpec core).Domain) (c : PublicHash.Cache core), ¬ P c →
      c t = none →
      (letI : MeasurableSpace ((publicHashSpec core).Range t) := ⊤;
        𝒟[($ᵗ (publicHashSpec core).Range t : ProbComp _)] {u | P (c.cacheQuery t u)} ≤ ε))
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (q : ℕ)
    (hq : HasHashQueryBound core adv q) :
    (letI : MeasurableSpace (RomOutcome vp core × PublicHash.Cache core) := ⊤;
      𝒟[romRunFull core adv] {z | P z.2} ≤ (q : ℝ≥0∞) * ε) := by
  let _ : MeasurableSpace (RomOutcome vp core × PublicHash.Cache core) := ⊤
  have hae : ∀ᵐ z ∂𝒟[romRunFull core adv],
      z ∈ {z : RomOutcome vp core × PublicHash.Cache core | P z.2} →
        z ∈ {z : RomOutcome vp core × PublicHash.Cache core |
          P z.2 ∧ QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} :=
    evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
      fun z hz hp => ⟨hp, enncard_le_of_hasHashQueryBound core adv q hq hz⟩
  refine (measure_mono_ae hae).trans ?_
  rw [romRunFull]
  exact evalDist_run_setOf_le_of_fresh_bound P hP ε hε hfresh (romGameCoreFull core adv) q

end SLHDSA.Security
