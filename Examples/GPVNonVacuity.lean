/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import VCVio.CryptoFoundations.GPVHashAndSign

/-!
# GPV #188 EUF-CMA: non-vacuity witness

The GPV hash-and-sign EUF-CMA bounds (`GPVHashAndSign.forgery_yields_collision_or_exact_match`
and the `euf_cma_*` corollaries) are stated under side conditions — PSF correctness and regularity,
a never-failing trapdoor sampler, the random-oracle "forger queries its forgery point" convention
(`ForgesQueriedPoint`), and a query-count bound (`signHashQueryBound`).  A conditional theorem says
nothing if its hypotheses are jointly uninhabitable: this file rules that out with a concrete
instance for which every side condition holds simultaneously, so the bounds are genuinely
non-vacuous.

The witness is the canonical bijective PSF over `Bool` with `PK = SK = Unit`: `eval` is the
identity, `trapdoorSample` returns its argument (the inverse of the identity), and the shortness
predicate is constantly `true`.  The adversary `adv` queries the random oracle once at a fixed point
and then forges at that same point, so its forgery key is constant and always cached — witnessing
`ForgesQueriedPoint`.

* `bijPSF_correct` / `bijPSF_regularity` — the PSF-side conditions.
* `bijPSF_hForge` — the forger queries its forgery point.
* `adv_signHashQueryBound` — the adversary makes `0` signing and `1` random-oracle queries.
* `gpv188_hyps_inhabited` — all four side conditions hold for the single instance
  `(bijPSF, hr, adv)`.
-/

open OracleComp OracleSpec

namespace Examples.GPVNonVacuity

/-- The canonical bijective PSF over `Bool`: `eval` is the identity, `trapdoorSample` returns its
argument (the inverse), and shortness is constantly `true`. -/
def bijPSF : PreimageSampleableFunction Unit Unit Bool Bool where
  eval := fun _ d => d
  trapdoorSample := fun _ _ r => pure r
  isShort := fun _ => true

/-- The trivial generable relation on `Unit` keys. -/
def hr : GenerableRelation Unit Unit (fun _ _ => true) where
  gen := pure ((), ())
  gen_sound := by intro x w _; rfl

/-- A query-then-forge adversary: it queries the random oracle once at `((), ())` and then forges
at that same `(salt, message) = ((), ())`, so its forgery key is the constant `((), ())`. -/
noncomputable def adv :
    SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Unit × Unit →ₒ Bool)))
        bijPSF hr Unit Unit) where
  main := fun _pk => do
    let _c ← (OracleComp.lift (OracleSpec.query
      (spec := (unifSpec + (Unit × Unit →ₒ Bool)) + (Unit →ₒ (Unit × Bool)))
      (.inl (.inr ((), ())))))
    pure ((), ((), false))

/-- The domain sampler witnessing regularity (uniform on `Bool`). -/
noncomputable def domainSample : Unit → ProbComp Bool := fun _ => ($ᵗ Bool)

/-- Helper: after running the fresh-flag handler on the random-oracle query at `((), ())`, the
resulting cache maps `((), ())` to a `some` value, for every initial state.  On a cache hit the
value is preserved; on a miss the handler writes `cacheQuery ((), ()) _`, `some` at `((), ())`. -/
lemma step_caches (pk : Unit)
    (s : ((Unit × Unit →ₒ Bool).QueryCache × Finset Unit) × Bool)
    (z : (Bool) × (((Unit × Unit →ₒ Bool).QueryCache × Finset Unit) × Bool))
    (hz : z ∈ support ((GPVHashAndSign.progGameRunImplNoRecFlagFresh bijPSF Unit Unit
      domainSample pk (.inl (.inr ((), ())))).run s)) :
    z.2.1.1 ((), ()) ≠ none := by
  rw [GPVHashAndSign.progGameRunImplNoRecFlagFresh_run_inl,
    GPVHashAndSign.progGameRunImplNoRec_run_read] at hz
  cases h : s.1.1 ((), ()) with
  | some v =>
      rw [h] at hz
      dsimp only at hz
      simp only [support_map, support_pure, Set.image_singleton] at hz
      have hz : z = (v, (s.1.1, s.1.2), s.2) := hz
      subst hz
      simp only [h, ne_eq, reduceCtorEq, not_false_eq_true]
  | none =>
      rw [h] at hz
      dsimp only at hz
      simp only [support_map] at hz
      obtain ⟨_, ⟨sd, _, rfl⟩, rfl⟩ := hz
      simp only
      rw [QueryCache.cacheQuery_self]
      exact Option.some_ne_none _

/-- The forger queries its forgery point: for every run in the support, the cache at the (constant)
forged key `((), ())` is non-`none`. -/
theorem bijPSF_hForge :
    GPVHashAndSign.ForgesQueriedPoint bijPSF hr Unit Unit adv domainSample := by
  unfold GPVHashAndSign.ForgesQueriedPoint
  intro pk z hz
  rw [show adv.main pk = (liftM (OracleSpec.query
      (spec := (unifSpec + (Unit × Unit →ₒ Bool)) + (Unit →ₒ (Unit × Bool)))
      (.inl (.inr ((), ()))))) >>= fun _ => pure ((), ((), false)) from rfl] at hz
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
  rw [support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨c, smid⟩, hmid, hrest⟩ := hz
  have hcache : smid.1.1 ((), ()) ≠ none := step_caches pk _ _ hmid
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
  subst hrest
  exact hcache

/-- The witness adversary makes exactly one random-oracle query and zero signing queries. -/
theorem adv_signHashQueryBound (pk : Unit) :
    GPVHashAndSign.signHashQueryBound Unit Unit (adv.main pk) 0 1 := by
  refine ⟨?_, ?_⟩
  · rw [show adv.main pk = (liftM (OracleSpec.query
        (spec := (unifSpec + (Unit × Unit →ₒ Bool)) + (Unit →ₒ (Unit × Bool)))
        (.inl (.inr ((), ()))))) >>= fun _ => pure ((), ((), false)) from rfl]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by decide), fun _ => trivial⟩
  · rw [show adv.main pk = (liftM (OracleSpec.query
        (spec := (unifSpec + (Unit × Unit →ₒ Bool)) + (Unit →ₒ (Unit × Bool)))
        (.inl (.inr ((), ()))))) >>= fun _ => pure ((), ((), false)) from rfl]
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr Nat.one_pos, fun _ => trivial⟩

/-- The witness PSF is correct: its trapdoor sampler is the identity, so every preimage hashes back
to its target and passes the (constantly true) shortness predicate. -/
theorem bijPSF_correct : bijPSF.Correct := by
  intro pk sk t x hx
  simp only [bijPSF, support_pure, Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨rfl, rfl⟩

/-- The witness PSF satisfies GPV regularity with `domainSample = $ᵗ Bool`: forward-sampling a short
preimage and hashing it forward is identical to sampling a uniform target and inverting it. -/
theorem bijPSF_regularity : bijPSF.Regularity := by
  refine ⟨domainSample, fun pk sk => ?_⟩
  simp only [bijPSF, domainSample, pure_bind]

/-- **Non-vacuity witness for the GPV #188 headline hypotheses.** For the concrete bijective PSF,
the generable relation `hr`, and the query-then-forge adversary `adv`, all the standard GPV side
conditions hold simultaneously: the forger queries its forgery point (`ForgesQueriedPoint`), the
adversary makes `0` signing and `1` random-oracle queries (`signHashQueryBound`), the PSF is correct
(`Correct`), and the PSF is regular (`Regularity`).  So the GPV EUF-CMA bounds are not vacuous. -/
theorem gpv188_hyps_inhabited :
    GPVHashAndSign.ForgesQueriedPoint bijPSF hr Unit Unit adv domainSample ∧
    (∀ pk : Unit, GPVHashAndSign.signHashQueryBound Unit Unit (adv.main pk) 0 1) ∧
    bijPSF.Correct ∧
    bijPSF.Regularity :=
  ⟨bijPSF_hForge, adv_signHashQueryBound, bijPSF_correct, bijPSF_regularity⟩

end Examples.GPVNonVacuity
