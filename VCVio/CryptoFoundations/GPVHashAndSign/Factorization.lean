/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.CollisionTelescope

/-! # GPV Hash-and-Sign: Per-Step Handlers for the signRunF Presentation

The regularity branch agreement and the concrete GPV per-step answer handlers of the fixed
signing-step recursion `signRunF`.
-/

public section

open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-! ## The `signRunF` presentation of the signing steps

The unconditional salt-inclusive bound `signRunF_measureTVDist_le_collisionBound` bounds the
real and programmed *salt-inclusive signing runs*, phrased over the fixed `qSign`-step recursion
`signRunF`. Matching the adaptive game runs `simulateQ impl (adv.main pk)` of
`SignatureAlg.unforgeableExperiment` to that fixed recursion would require front-loading the
adversarially interleaved signing salts (a deferred-sampling factorization). That factorization is
not established, and it is not on the path of the headline bounds: the sign-then-hash hop
`gpv_measureTVDist_real_programmed_le_collisionBound` is proved by the inline-salt flag route of
`FlagHandlers.lean` (`gpv_measureTVDist_orig_run_le_prEvent_flag`,
`gpv_orig_flag_le_collisionBound`).

This file records the per-step ingredients of the `signRunF` presentation:

* `regularity_signAnswer_agree`: under PSF regularity the *real* RO-cache-miss answer `(c, s)`
  (fresh uniform target `c ← $ᵗ Range`, then `s ← trapdoorSample pk sk c`) and the *programmed*
  answer (`s ← domainSample pk`, target `eval pk s`) are equal in distribution. This is the
  regularity equation transposed, and is the off-collision branch agreement
  `signRunF_measureTVDist_le_saltSeq_aux` consumes.
* the concrete GPV per-step handlers `gpvStepReal` / `gpvStepProg` together with their
  off-collision agreement `gpvStep_agree`. -/

omit [DecidableEq Range] in
/-- **Regularity branch-agreement bridge.** Under PSF regularity, the real cache-miss
signing answer and the programmed signing answer agree in distribution.

The real answer at a fresh salt — produced by the lazy random oracle on a cache miss — draws a fresh
uniform target `c ← $ᵗ Range` and then a short preimage `s ← trapdoorSample pk sk c`, returning the
pair `(c, s)`. The programmed answer draws `s ← domainSample pk` and uses the target `eval pk s`,
returning `(eval pk s, s)`. PSF regularity (`psf.Regularity`) states exactly that these two joint
distributions coincide, so this is the regularity equation read right-to-left.

This is the GPV-concrete witness for the off-collision branch-agreement hypothesis `h_step` of
`signRunF_measureTVDist_le_saltSeq` / `signRunF_measureTVDist_le_collisionBound`: off the per-step
salt collision
`r ∉ c j`, the real and programmed per-signing-step answer handlers agree in distribution. -/
theorem regularity_signAnswer_agree (hreg : psf.Regularity) (pk : PK) (sk : SK) :
    ∃ domainSample : PK → ProbComp Domain,
      (do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
          : ProbComp (Range × Domain)) =ᵈ
        (do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain)) := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨domainSample, (h pk sk).symm⟩

/-! ## Concrete GPV `signRunF` handlers

This section pins GPV-concrete per-step handlers for the `signRunF` presentation and proves their
*structural* property: the real and programmed steps agree in distribution off the per-step salt
collision under regularity. The run-level equalities identifying the adaptive game runs with
`signRunF` runs are not established here (see the section above); the per-body splices below are
the signing-step ingredients such a factorization would consume.

The handler state is the lazy random-oracle cache `(Salt × M →ₒ Range).QueryCache`; both step
handlers update it at the freshly drawn salt `r` and the `n`-th signing message `msgs n`. The
`stepReal` handler mirrors the real signing oracle's *cache-miss* branch: draw a uniform target
`c ← $ᵗ Range`, draw the trapdoor preimage, and cache `c`. The `stepProg` handler mirrors the
sign-then-hash simulator: forward-sample a short preimage `s ← domainSample pk` and program the
cache entry to `psf.eval pk s`. -/

open Classical in
/-- **Real GPV signing step (cache-miss branch).** At signing step `n` with random-oracle cache
`cache` and freshly drawn salt `r`, draw a uniform target `c ← $ᵗ Range`, draw a trapdoor preimage
of `c`, and record `(r, msgs n) ↦ c` in the cache. This is the per-step handler used as `stepReal`
in the GPV `signRunF` presentation of the real game run. -/
noncomputable def gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) :
    ℕ → (Salt × M →ₒ Range).QueryCache → Salt → ProbComp ((Salt × M →ₒ Range).QueryCache) :=
  fun n cache r => do
    let c ← ($ᵗ Range)
    let _s ← psf.trapdoorSample pk sk c
    pure (cache.cacheQuery (r, msgs n) c)

open Classical in
/-- **Programmed GPV signing step (sign-then-hash branch).** At signing step `n` with random-oracle
cache `cache` and freshly drawn salt `r`, forward-sample a short preimage `s ← domainSample pk` and
record `(r, msgs n) ↦ psf.eval pk s` in the cache. This is the per-step handler used as `stepProg`
in the GPV `signRunF` presentation of the programmed (simulator) run. -/
@[expose]
noncomputable def gpvStepProg (pk : PK) (domainSample : PK → ProbComp Domain) (msgs : ℕ → M) :
    ℕ → (Salt × M →ₒ Range).QueryCache → Salt → ProbComp ((Salt × M →ₒ Range).QueryCache) :=
  fun n cache r => do
    let s ← domainSample pk
    pure (cache.cacheQuery (r, msgs n) (psf.eval pk s))

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real/programmed GPV step distributional agreement.** Under PSF regularity (witnessed by the
forward sampler `domainSample` of `psf.Regularity`), the real and programmed per-step handlers agree
as output distributions at every step `n`, cache, and salt `r`.

Both handlers update the same cache slot `(r, msgs n)` with the first component of a `(target,
preimage)` pair; the real handler draws that pair as `(c, s)` with `c ← $ᵗ Range`, `s ←
trapdoorSample pk sk c`, while the programmed handler draws it as `(eval pk s, s)` with `s ←
domainSample pk`. PSF regularity equates exactly these two joint distributions, so projecting onto
the cache update preserves the equality. This agreement is in fact *unconditional* in `r` (it does
not require `r ∉ c n`), which is stronger than the obligation's off-collision conjunct demands. -/
theorem gpvStep_agree (pk : PK) (sk : SK) (msgs : ℕ → M)
    (domainSample : PK → ProbComp Domain)
    (hreg : (do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain)) =ᵈ
      (do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
          : ProbComp (Range × Domain)))
    (n : ℕ) (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) :
    gpvStepReal psf M Salt pk sk msgs n cache r =ᵈ
      gpvStepProg psf M Salt pk domainSample msgs n cache r := by
  unfold gpvStepReal gpvStepProg
  set proj : Range × Domain → (Salt × M →ₒ Range).QueryCache :=
    fun cs => cache.cacheQuery (r, msgs n) cs.1 with hproj
  have hR : (($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>=
              fun _s => (pure (cache.cacheQuery (r, msgs n) c) : ProbComp _))
        = ((($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>= fun s => pure (c, s)) >>=
            fun cs => pure (proj cs)) := by simp [hproj]
  have hP : (domainSample pk >>=
              fun s => (pure (cache.cacheQuery (r, msgs n) (psf.eval pk s)) : ProbComp _))
        = ((domainSample pk >>= fun s => pure (psf.eval pk s, s)) >>=
            fun cs => pure (proj cs)) := by simp [hproj]
  change (($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>=
      fun _s => (pure (cache.cacheQuery (r, msgs n) c) : ProbComp _)) =ᵈ
    (domainSample pk >>= fun s =>
      (pure (cache.cacheQuery (r, msgs n) (psf.eval pk s)) : ProbComp _))
  rw [hR, hP]
  exact hreg.symm.bind_left _

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real GPV signing-body cache splice (cache-miss key).** One real signing-query body, run
through the lazy random oracle at a *missing* cache key `(r, msgs n)`, produces a recorded-cache
transition distributed exactly as the concrete `signRunF` real step `gpvStepReal` at the (already
fixed) salt `r`.

The signing body queries the random oracle at `(r, msgs n)`; on the cache miss `cache (r, msgs n) =
none` the oracle draws a fresh uniform target `u ← $ᵗ Range`, records `(r, msgs n) ↦ u`, and returns
`u`; the body then draws the trapdoor preimage and yields the updated cache. The handler
`gpvStepReal` draws the same uniform target `c ← $ᵗ Range`, the same trapdoor preimage, and records
`(r, msgs n) ↦ c` — so the two recorded-cache distributions coincide. This is the *per-body splice*
of the adaptive→`signRunF` fold factorization (the signing-step case of the real run-equality
`realRun =ᵈ signRunF gpvStepReal c qSign …`): it recasts one inline signing-oracle body, on a
fresh-salt cache miss, as the concrete `signRunF` real step, with the fresh salt `r` front-loaded
out of the body. It is *pinned* to the concrete `randomOracle` and `gpvStepReal`, requires only the
cache-miss side condition `hmiss` (guaranteed for a fresh salt), and is unconditional otherwise. -/
theorem evalDistEq_gpvSignBody_run_eq_gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) (n : ℕ)
    (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt)
    (hmiss : cache (r, msgs n) = none) :
    (do
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msgs n)).run cache
        let _s ← psf.trapdoorSample pk sk p.1
        pure p.2 : ProbComp ((Salt × M →ₒ Range).QueryCache)) =ᵈ
      gpvStepReal psf M Salt pk sk msgs n cache r := by
  unfold gpvStepReal
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) (r, msgs n)).run cache
        = (fun u => (u, cache.cacheQuery (r, msgs n) u)) <$>
            (uniformSampleImpl (spec := (Salt × M →ₒ Range)) (r, msgs n))
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  rw [show (uniformSampleImpl (spec := (Salt × M →ₒ Range)) (r, msgs n))
        = ($ᵗ Range : ProbComp Range) from rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind, EvalDistEq.refl]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Programmed GPV signing-body cache splice (simulator signing query).** One programmed
simulator signing-query body — the `signImpl` handler of `progGameRun`, which draws a fresh salt
`r ← $ᵗ Salt`, forward-samples a short preimage `s ← domainSample pk`, programs the random-oracle
cache entry `(r, msg) ↦ psf.eval pk s`, updates the preimage record, and returns `(r, s)` — has its
recorded random-oracle *cache component* (with the salt draw front-loaded, and the returned
signature and the auxiliary preimage record dropped) distributed exactly as the salt-prefixed
concrete `signRunF` programmed step: draw the same fresh salt `r ← $ᵗ Salt`, then apply
`gpvStepProg` at that `r`.

This is the programmed-side dual of `evalDistEq_gpvSignBody_run_eq_gpvStepReal`, and the
signing-step
case of the *programmed* run-equality
`progGameRun … =ᵈ signRunF gpvStepProg c qSign …` of the fold
factorization. It is *pinned* to the concrete `progGameRun` signing body
and the concrete `gpvStepProg`: the cache transition
`cache ↦ cache.cacheQuery (r, msgs n) (psf.eval pk s)`
on both sides is the same, the salt draw is the same front-loaded `$ᵗ Salt`, and `domainSample` is
the shared programming randomness. No probability-mass averaging is performed; the equality is the
exact recasting of one inline simulator signing body — with its salt front-loaded — as one
`signRunF` programmed step. The auxiliary preimage record `((Salt × M) → Option Domain)` of
`progGameRun`'s state, which `gpvStepProg` does not carry, is dropped here (it is
collision-extraction bookkeeping, irrelevant to the random-oracle cache distribution that the
sign-then-hash hop compares; it is reattached at the run level, not the per-step level). -/
theorem evalDistEq_gpvSignBody_run_eq_gpvStepProg (pk : PK) (domainSample : PK → ProbComp Domain)
    (msgs : ℕ → M) (n : ℕ)
    (cache : (Salt × M →ₒ Range).QueryCache) (pre : (Salt × M) → Option Domain) :
    (do
        -- The actual `progGameRun` simulator signing body (`signImpl`), with the fresh salt draw
        -- front-loaded, run on state `(cache, pre)`; project out the random-oracle cache component
        -- (dropping the returned signature and the auxiliary preimage record).
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← ((do
            let s ← (domainSample pk : ProbComp Domain)
            let v := psf.eval pk s
            let st ← get
            set ((st.1.cacheQuery (r, msgs n) v,
              fun t' => if t' = (r, msgs n) then some s else st.2 t')
                : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain))
            pure (r, s) :
              StateT ((Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain))
                ProbComp (Salt × Domain)).run (cache, pre))
        pure p.2.1 : ProbComp ((Salt × M →ₒ Range).QueryCache)) =ᵈ (do
          let r ← ($ᵗ Salt : ProbComp Salt)
          gpvStepProg psf M Salt pk domainSample msgs n cache r
            : ProbComp ((Salt × M →ₒ Range).QueryCache)) := by
  unfold gpvStepProg
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    StateT.run_map, bind_pure_comp, map_pure, Functor.map_map, monadLift_self, EvalDistEq.refl]

end GPVHashAndSign
