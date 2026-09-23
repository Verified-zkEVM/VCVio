/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

public import VCVio.CryptoFoundations.GPVHashAndSign.Reservoir

/-! # GPV Hash-and-Sign: Security Bounds

The forgery dichotomy and the headline EUF-CMA bounds. The collision branch is extracted here;
the exact-match branch comes from the reservoir extraction in `GPVHashAndSign.Reservoir`, which
builds on the trapdoor-recording run projections in `GPVHashAndSign.TrapProjection`.

The headline bounds here, `euf_cma_split_bound` and `euf_cma_collision_bound`, carry the
random-oracle convention `ForgesQueriedPoint` as a hypothesis. They are the primitive forms that
the append-forgery-query compiler chains through; the public endpoints for consumers are the
all-adversaries corollaries `euf_cma_split_bound_of_queryBound` and
`euf_cma_collision_bound_of_queryBound` in `AppendQuery.lean`, whose only structural hypothesis on
the adversary is the query bound.
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

open Classical in
omit [Fintype Salt] in
/-- **Step 2 (collision extraction): the keygen-averaged programmed freshness verify-Bool game is
bounded by the collision and exact-match reduction advantages.**

In the programmed sign-then-hash game `progGameVerifyFresh`, every random-oracle entry was
programmed as `psf.eval pk s` for a hidden short preimage `s ← domainSample pk`.  Under `hForge` the
forgery `(msg, (r, s⋆))` lands on a programmed entry, so the verification read is a cache hit
returning `psf.eval pk sHidden` for the simulator's hidden preimage `sHidden` at `(r, msg)`; a
verifying fresh forgery therefore satisfies `psf.eval pk s⋆ = psf.eval pk sHidden` with both
preimages short (the forged one by the verifier's `isShort` check, the hidden one by `hcorrect` and
`hreg`).  This splits into:

* the **distinct-preimage branch** `sHidden ≠ s⋆`, a collision under `psf.eval` extracted by the
  collision reduction `reduction` (which records the hidden preimage at each programmed point and
  returns `(sHidden, s⋆)`), bounding that mass by `collisionFindingAdvantage (reduction …)`; and
* the **exact-match branch** `sHidden = s⋆`, where the forgery reproduces the simulator's hidden
  preimage; the programmed-preimage reduction `programmedPreimageReduction` embeds its target `y` at
  one uniformly chosen programmed entry (reservoir sampling over the at most `qSign + qHash`
  entries), winning when the embedded entry is the forged point, which costs the explicit
  multi-target factor `qSign + qHash`.

This is the Step-2 collision extraction of the GPV proof, stated pinned over the concrete
programmed forgery game and the concrete reductions. -/
theorem gpv_progGameVerifyFreshAvg_le_collisionAdv_add_preimageAdv [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk) (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[= true | (𝒮[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
        progGameVerifyFresh psf hr M Salt adv domainSample pksk.1]
      ≤ collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) := by
  classical
  -- Reduce the keygen-average to a per-key `(pk, sk)` bound via the averaging skeleton SL-A,
  -- then discharge that per-key bound (the distinct-collision transfer + the reservoir exact-match
  -- bound) — the Step-2 collision extraction.
  refine gpv_progGameVerifyFreshAvg_le_of_perKey psf hr M Salt qSign qHash adv domainSample ?_
  intro pksk hmem
  -- Lift the game success onto the combined run, split into the distinct and exact-match branches,
  -- transfer the distinct branch to the collision reduction, and hand the exact branch to the
  -- reservoir bound.
  rw [progGameVerifyFresh_eq_probEvent_combined psf hr M Salt domainSample pksk.1 adv,
    reduction_collision_eq_probEvent_combined psf hr M Salt domainSample pksk.1 adv]
  refine le_trans (probEvent_mono (fun w _ hw => ?_) :
      _ ≤ Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
          ((decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) ≠ some w.1.1.2.2) ∨
            ((decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2) | _]) ?_
  · by_cases heq : w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2
    · exact Or.inr ⟨hw, heq⟩
    · exact Or.inl ⟨hw, heq⟩
  refine le_trans (probEvent_or_le _ _ _) ?_
  gcongr
  · exact gpv_perKey_distinct_le_collision psf hr M Salt domainSample pksk.1 pksk.2
      (hcorrect pksk.1 pksk.2 hmem) (hreg pksk.1 pksk.2 hmem) adv hForge
  · exact gpv_perKey_exactMatch_le_reservoir psf hr M Salt domainSample pksk.1 pksk.2 qSign qHash
      adv (hreg pksk.1 pksk.2 hmem) (hNF pksk.1 pksk.2 hmem) hForge (hQ pksk.1)

/-- **Full split GPV game-hop**: every successful fresh forgery falls into one of two cases.

1. **Distinct-preimage branch:** the forgery differs from the simulator's hidden programmed
   preimage at the forged point, yielding a collision under `psf.eval`.
2. **Exact-match branch:** the forgery exactly reproduces the simulator's hidden programmed
   preimage at that point. To capture this branch, the reduction guesses one of the at most
   `qSign + qHash` programmed entries and turns success there into a win in the single-target
   programmed-preimage experiment.

The only additional failure mode is a salt collision, bounded by `collisionBound`.

The honest trapdoor sampler is assumed total (`hNF`): for every key pair and target the sampler
`psf.trapdoorSample` never fails (`NeverFail`).  This is the standard GPV08 well-formedness
condition that the trapdoor inversion is a genuine distribution; it is the hypothesis that keeps
probability mass during the real↔programmed sign-then-hash hop and is not implied by `hcorrect`
(which constrains only the *support* of the sampler) nor by `hreg` (which equates only the *total
masses* of the two joint distributions).

The forger is assumed to query its forgery point (`hForge`, `ForgesQueriedPoint`): the standard
ROM well-formedness condition that the forgery lands on a programmed random-oracle entry, so the
collision/exact-match extraction observes the simulator's hidden preimage at that point. -/
theorem forgery_yields_collision_or_exact_match [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk) (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    SignatureAlg.unforgeableAdvantage (runtime M Salt) adv ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) +
        collisionBound Salt qSign qHash := by
  refine le_trans (gpv_advantage_le_progGameVerifyFreshAvg_add_collisionBound psf hr M Salt
    qSign qHash adv domainSample hreg hNF hQ) ?_
  gcongr
  exact gpv_progGameVerifyFreshAvg_le_collisionAdv_add_preimageAdv psf hr M Salt
    hcorrect qSign qHash adv domainSample hreg hNF hForge hQ

/-- **Collision-only specialization of the GPV split bound under a PSF preimage min-entropy
bound.**  This is `forgery_yields_collision_or_exact_match` with the exact-match
(programmed-preimage) branch controlled by an explicit preimage min-entropy / one-wayness bound
`εpp`: the adversary's chance of reproducing the simulator's hidden short preimage at a programmed
point is at most `εpp` (`hMinEntropy`), so the multi-target exact-match contribution is at most
`(qSign + qHash) · εpp`.  It is *derived* from the split bound and carries no independent proof
obligation.

The exact-match term is *bounded*, not eliminated: `programmedPreimageAdvantage ≥ 1 / |Domain| > 0`
for a finite domain (reproducing a sampled preimage is always possible with nonzero probability),
so a clean collision-only bound (`εpp = 0`) is unsatisfiable.  Specializing `εpp` to a concrete PSF
preimage min-entropy bound (e.g. for Falcon) yields the quantitative collision bound. -/
theorem forgery_yields_collision [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk) (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (εpp : ℝ≥0∞)
    (hMinEntropy : programmedPreimageAdvantage (psf := psf) (hr := hr)
      (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) ≤ εpp) :
    SignatureAlg.unforgeableAdvantage (runtime M Salt) adv ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) * εpp +
        collisionBound Salt qSign qHash := by
  refine le_trans (forgery_yields_collision_or_exact_match psf hr M Salt hcorrect qSign qHash
    adv domainSample hreg hNF hForge hQ) ?_
  gcongr

/-- **Collision-style GPV PFDH bound in the random-oracle model, under a preimage min-entropy
bound**.

For any adversary `A` making at most `qSign` signing queries against the GPV hash-and-sign
scheme with a correct PSF and `k`-bit salts, and making at most `qHash` random-oracle queries,
the collision-finding reduction `B = reduction psf hr M Salt A domainSample` satisfies:

  `Adv^{EUF-CMA}(A) ≤ Adv^{collision}(B) + (qSign + qHash) · εpp + (qSign + qHash)² / (2 · |Salt|)`

where `εpp` bounds the exact-match (programmed-preimage) branch: the chance that an adversary
reproduces the simulator's hidden short preimage at a programmed point is at most `εpp`
(`hMinEntropy`), the PSF preimage min-entropy / one-wayness assumption. The distinct-preimage
branch gives the collision term; the exact-match branch the `(qSign + qHash) · εpp` term. This is a
specialization of `euf_cma_split_bound` and is derived from it; the exact-match term is *bounded*,
not dropped, since `programmedPreimageAdvantage ≥ 1 / |Domain| > 0` for a finite domain.

The salt-collision term `(qSign + qHash)² / (2 · |Salt|)` is `collisionBound`, the closed birthday
form of the union sum `∑_{j < qSign} (j + qHash) / |Salt|` the telescope establishes: a fresh
signing salt colliding with any previously recorded `(salt, message)` random-oracle input (a
prior signing salt or an adversary hash query). It is the constant this theorem proves; the
`collisionBound` docstring records how it relates to the GPV08 and [FGdG+25] constants. For Falcon
with 40-byte salts (`|Salt| = 2^320`), this is `2^{-191}` even for `qSign = qHash = 2^64`.

This form carries the `ForgesQueriedPoint` convention as a hypothesis and leaves `εpp` abstract.
The endpoint for consumers is `euf_cma_collision_bound_of_queryBound`, which discharges the
convention by the append-forgery-query compiler and prices `εpp` by the trapdoor guessing
probability.

References: GPV08 Section 6; BDF+11 for the QROM extension. -/
theorem euf_cma_collision_bound [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk)
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (εpp : ℝ≥0∞)
    (hMinEntropy : programmedPreimageAdvantage (psf := psf) (hr := hr)
      (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) ≤ εpp) :
    SignatureAlg.unforgeableAdvantage (runtime M Salt) adv ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) * εpp +
        collisionBound Salt qSign qHash :=
  forgery_yields_collision psf hr M Salt hcorrect qSign qHash adv domainSample hreg hNF hForge hQ
    εpp hMinEntropy

/-- **Split GPV PFDH bound in the random-oracle model**.

This theorem makes both branches of the GPV proof explicit:

- a collision term for the distinct-preimage branch, for the reduction `reduction`,
- a programmed-preimage replay term for the exact-match branch, for the reduction
  `programmedPreimageReduction`, with the explicit multi-target factor `qSign + qHash`,
- and the birthday salt-collision term.

It is the most honest generic statement available from the current API, before any additional
PSF-specific min-entropy lemma collapses the exact-match branch into the collision branch.

This form carries the `ForgesQueriedPoint` convention as a hypothesis; the endpoint for consumers
is `euf_cma_split_bound_of_queryBound`, which discharges it for every adversary at one extra hash
query via the append-forgery-query compiler. -/
theorem euf_cma_split_bound [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk)
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒮[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒮[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    SignatureAlg.unforgeableAdvantage (runtime M Salt) adv ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) +
        collisionBound Salt qSign qHash :=
  forgery_yields_collision_or_exact_match psf hr M Salt hcorrect qSign qHash adv domainSample hreg
    hNF hForge hQ

end GPVHashAndSign
