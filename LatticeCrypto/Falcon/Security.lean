/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.Falcon.Scheme
public import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
public import VCVio.OracleComp.Constructions.RetryLoop
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Falcon Security

This file states conditional security bounds for an idealized Falcon rejection-loop signer in the
GPV hash-and-sign model, with the trapdoor sampler priced per signing attempt.

## Scope: an idealized Falcon/GPV model

The theorems here are about an **idealized Falcon model**, precisely:

- The scheme is `falconRetrySignatureAlg`, the generic GPV hash-and-sign scheme (`GPVHashAndSign`)
  over the rejection-loop signer `falconRetryPSF`, which repeats `signAttempt` at one salt and one
  target up to an attempt budget and returns `default` when the budget runs out. The fuel-bounded
  signer `sign` instead draws a fresh salt for every retry. Signatures carry the full `(s₁, s₂)`
  preimage; the compressed `s₂`-only wire encoding and byte-level (de)serialization of FN-DSA are
  not modeled.
- The trapdoor sampler enters only through an ideal preimage-sampleable abstraction (`idealPSF`)
  sharing the deterministic `eval`/`isShort` of `falconPSF`. The concrete-to-ideal gap is the named
  total-variation hypothesis `attemptTransport`, and floating-point `ffSampling` with its precision
  analysis is not modeled. A `ProbComp` has finite support, so `idealPSF` can only approximate the
  coset Gaussian that GPV08 and [FGdG+25] analyze; `attemptTransport` has to price that gap too.
- Verification correctness is proved for the fuel-bounded signer `sign`, not for the modelled
  schemes: `verify_sign_correct` takes the codec round-trip and the coset identity
  (`s₁ + s₂ · h = c` on honest keys) as hypotheses, and `Extern.Falcon.SignCorrectness`
  discharges both at the exact-FFT concrete primitives from key validity. Through the
  floating-point inverse-FFT rounding in `Falcon.fromFFTPreimage` the coset identity remains
  a hypothesis.
- No cost model is attached: the reductions are constructed explicitly but their polynomial
  runtime is not machine-checked. Besides the caller-supplied domain sampler `domainSample`,
  they perform no exhaustive search and no noncomputable steps beyond the ambient probabilistic
  semantics.
- `hReg` requires `domainSample` to match the ideal sampler's joint distribution exactly. The
  collision term is a hardness assumption only when `domainSample` needs no trapdoor. The only
  `domainSample` in the repository, in `LatticeCryptoTest.Falcon.NonVacuity`, samples with the
  basis. A discrete Gaussian does not meet the exact form either, since its image is only
  statistically close to uniform; regularity up to an additive statistical term is not
  formalized.

## The bounds

`euf_cma_security` is the split GPV bound (`GPVHashAndSign.euf_cma_split_bound_of_queryBound`): the
EUF-CMA advantage is at most the Falcon-PSF collision advantage sampled from the scheme's own key
distribution (`collisionFindingAdvantage_eq_ntruPSF`), plus an exact-match branch at an explicit
multi-target factor, plus the salt birthday bound `GPVHashAndSign.collisionBound`, plus the sampler
loss `qSign · (ε_step / (1 − pRej) + pRej ^ maxAttempts)`
(`measureTVDist_falconRetryPSF_trapdoorSample_le`): the per-attempt gap `ε_step` accumulated over
the expected retry count, plus the attempt-budget exhaustion mass. For that loss to be small at a
signing budget of `2^64`, `ε_step` has to be far below `2^-64`. `euf_cma_collision_security`
discharges the exact-match branch by the ideal sampler's guessing bound `idealSamplerGuessBound`.

## What the bounds give at Falcon's parameters

Every headline here is conditional, and with what is proved so far none is below one at
Falcon's parameters:

- **Exact-match term.** The only guessing bound proved is `εpp = 1`
  (`idealSamplerGuessBound_one`), at which the exact-match term of `euf_cma_collision_security`
  and `euf_cma_collision_security_ntruSIS` is `qSign + qHash + 1`.
  `LatticeCrypto.Falcon.SamplerMinEntropy` bounds the point mass of `ffSampling`'s output
  before reduction modulo `q`; the bound for the reduced output is open.
- **Sampler term.** No `ε_step` is proved for Falcon's floating-point sampler. `ε_step = 0` is
  reachable by taking Falcon's own attempt as the ideal one, which moves the precision question into
  `hReg` and the guessing bound.

`LatticeCryptoTest.Falcon.NonVacuity` instantiates the hypotheses of `euf_cma_security` at an NTRU
key with a genuinely rejecting sampler, and those of `euf_cma_collision_security_ntruSIS` at
`εpp = 1`.

## Relation to the literature

[FGdG+25] Theorem 1 bounds Falcon+ by a Rényi-divergence accumulation of the per-query sampler
and random-oracle simulation gaps over all preimage-sampling calls including retries; [Jia+26]
sharpens the per-basis divergence, and [TWFalcon] measures the floating-point precision the
sampler actually achieves. The theorems here replace the Rényi accumulation by a
total-variation accumulation of a named per-attempt gap, take the salt term as the birthday
bound of GPV08 Proposition 6.2 rather than [FGdG+25]'s `Q_s · (C_s + Q_H) / 2^k`, and formalize
no concrete bit-security figure.

## References

- [FGdG+25]: Fouque, Gajland, de Groote, Janneck, Kiltz. "A Closer Look at Falcon."
  ePrint 2024/1769, updated 2025. First concrete security proof for Falcon+.
- [Jia+26]: Jia, Zhang, Yu, Tang. "Revisiting the Concrete Security of Falcon-type
  Signatures." ePrint 2026/096. Basis-specific analysis eliminating the 7-bit loss.
- [TWFalcon]: Halmans et al. "TWFalcon: Triple-Word Arithmetic for Falcon."
  ePrint 2025/1991. Shows binary64 misses the published Rényi threshold.
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008, Propositions 6.1–6.2.
- [Pre17]: Prest. ASIACRYPT 2017. Rényi-based precision analysis for Klein's sampler.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ### Correctness -/

/-- **Falcon verification correctness, conditional on the sampler landing on the coset.**

If the fuel-bounded signer returns a signature, `verify` accepts it, given two facts about the
primitives at the honest key:

1. `hcompress`: the codec round-trips (the `compress_decompress` law of `Primitives.Laws`,
   a theorem for the concrete codec: `Falcon.Concrete.decompress_compress`);
2. `hpreimage`: every output of the trapdoor sampler is a preimage of its target,
   `s₁ + s₂ · h = c`.

Hypothesis 2 is the coset obligation of the FFT pipeline. `fromFFTPreimage` rounds an inverse
FFT and returns `(c − v₀, −v₁)`. For a valid basis, a sufficient condition is that the rounded
`v` equals the integer lattice point `z · B`; coordinatewise error strictly below `1/2` before
rounding establishes that condition. The coset identity itself is the hypothesis here, so exact
FFT arithmetic and a certified numerical implementation can discharge it separately. Neither the
NTRU equation nor `validKeyPair` is needed in this theorem: the signer emits only attempts that
passed the norm check, and that check is `verify`'s own. -/
theorem verify_sign_correct (pk : PublicKey p) (sk : SecretKey p) (msg : List Byte)
    (maxAttempts : ℕ) (sig : Signature)
    (hcompress : ∀ (s : IntPoly p.n) (slen : ℕ) (bytes : List Byte),
      prims.compress s slen = some bytes → prims.decompress bytes slen = some s)
    (hpreimage : ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      x ∈ support ((falconPSF p prims).trapdoorSample pk sk c) →
        (falconPSF p prims).eval pk x = c)
    (hsig : some sig ∈ support (sign p prims pk sk msg maxAttempts)) :
    verify p prims pk msg sig = true := by
  induction maxAttempts with
  | zero =>
    simp only [sign, support_pure, Set.mem_singleton_iff] at hsig
    exact absurd hsig (by simp)
  | succ k ih =>
    rw [sign, mem_support_bind_iff] at hsig
    obtain ⟨salt, _hsalt, hsig⟩ := hsig
    rw [mem_support_bind_iff] at hsig
    obtain ⟨r, hr, hsig⟩ := hsig
    match r, hr, hsig with
    | none, _hr, hsig => exact ih hsig
    | some (s₁, s₂), hr, hsig =>
      dsimp only at hsig
      cases hcomp : prims.compress (rqToIntPolyCentered s₂) p.sbytelen with
      | none =>
        rw [hcomp] at hsig
        exact ih hsig
      | some comp =>
        rw [hcomp] at hsig
        simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hsig
        subst hsig
        -- The accepting attempt is a `trapdoorSample` output that passed the norm check.
        set c := prims.hashToPointForPublicKey pk.h salt msg with hc
        rw [signAttempt, mem_support_bind_iff] at hr
        obtain ⟨x, hx, hr⟩ := hr
        have hshort_eval :
            (s₁, s₂) ∈ support ((falconPSF p prims).trapdoorSample pk sk c) ∧
              (falconPSF p prims).isShort (s₁, s₂) = true := by
          by_cases hshort : (falconPSF p prims).isShort x = true
          · rw [ite_eq_left hshort, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr
            subst hr
            exact ⟨hx, hshort⟩
          · rw [ite_eq_right hshort, support_pure, Set.mem_singleton_iff] at hr
            exact absurd hr (by simp)
        obtain ⟨hmem, hshort⟩ := hshort_eval
        have heval : (falconPSF p prims).eval pk (s₁, s₂) = c := hpreimage c (s₁, s₂) hmem
        -- `verify` decompresses to the same `s₂`, recomputes the same `s₁`, and runs the norm
        -- check the attempt already passed.
        have hdec := hcompress _ _ _ hcomp
        unfold verify
        simp only [hdec]
        rw [toRq_rqToIntPolyCentered]
        have hs1 : c - negacyclicMul s₂ pk.h = s₁ := by
          rw [← heval]
          change s₁ + negacyclicMul s₂ pk.h - negacyclicMul s₂ pk.h = s₁
          apply LatticeCrypto.Poly.ext_get_eq
          intro i
          calc (s₁ + negacyclicMul s₂ pk.h - negacyclicMul s₂ pk.h).get i
              = (s₁ + negacyclicMul s₂ pk.h).get i - (negacyclicMul s₂ pk.h).get i :=
                LatticeCrypto.NegacyclicRing.coeff_sub (coeffRing p.n) _ _ i
            _ = s₁.get i + (negacyclicMul s₂ pk.h).get i - (negacyclicMul s₂ pk.h).get i :=
                congrArg (· - (negacyclicMul s₂ pk.h).get i)
                  (LatticeCrypto.NegacyclicRing.coeff_add (coeffRing p.n) _ _ i)
            _ = s₁.get i := add_sub_cancel_right _ _
        change decide (pairL2NormSq (c - negacyclicMul s₂ pk.h) s₂ ≤ p.betaSquared) = true
        rw [hs1]
        exact hshort

/-! ### NTRU-SIS Hardness Assumption -/

/-- The NTRU-SIS problem: given `h ∈ R_q` (the Falcon public key), find a short nonzero
`(s₁, s₂) ∈ R_q²` satisfying `s₁ + s₂ · h = 0 mod q` with `‖(s₁, s₂)‖₂² ≤ 4·⌊β²⌋`.

This is the lattice problem underlying Falcon's security. It is an instance of
the generic SIS problem where the matrix is the single-row matrix `[I | h]`
over the cyclotomic ring `R_q = ℤ_q[x]/(x^n + 1)`.

The norm target is `4·betaSquared`, not `betaSquared`: a kernel vector produced from a
Falcon-PSF collision is the difference `x - x'` of two `β`-short preimages, so its squared
`ℓ₂` norm is at most `(‖x‖₂ + ‖x'‖₂)² ≤ (2β)² = 4·betaSquared`. The
`ntruPSFCollisionProblem → ntruSISProblem` translation realizing this target is
`Falcon.ntruSISProblem_isValid_sub` (witness level) and
`Falcon.advantage_le_ntruSISProblemKeyed` (advantage level, at the honest key distribution
`ntruSISProblemKeyed`) in
`LatticeCrypto.Falcon.SISBridge`; the remaining distance between the honest key
distribution and this problem's uniform challenge is a decisional-NTRU assumption. -/
noncomputable def ntruSISProblem :
    SIS.Problem (Rq p.n) (Rq p.n × Rq p.n) where
  sampleChallenge := $ᵗ (Rq p.n)
  isValid h x :=
    decide (x ≠ (0, 0)) &&
    decide (pairL2NormSq x.1 x.2 ≤ 4 * p.betaSquared) &&
    decide (x.1 + negacyclicMul x.2 h = 0)

/-- The direct Falcon PSF collision problem induced by the generic GPV reduction.

The challenger samples a Falcon public key from the same key distribution used by the
signature scheme, and the adversary must produce two distinct short preimages with the
same image under the Falcon PSF `(s₁, s₂) ↦ s₁ + s₂ · h`.

This is the immediate hardness target of the collision-style GPV bound before any further
translation to a kernel-vector NTRU-SIS formulation. -/
noncomputable def ntruPSFCollisionProblem
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p)) :
    SIS.Problem (PublicKey p) ((Rq p.n × Rq p.n) × (Rq p.n × Rq p.n)) where
  sampleChallenge := do
    let (pk, _) ← hr.gen
    pure pk
  isValid pk xs :=
    decide (xs.1 ≠ xs.2) &&
    decide ((falconPSF p prims).eval pk xs.1 = (falconPSF p prims).eval pk xs.2) &&
    (falconPSF p prims).isShort xs.1 &&
    (falconPSF p prims).isShort xs.2

/-! ### EUF-CMA Security -/

/-- The Falcon-PSF collision experiment **is** the `ntruPSFCollisionProblem` search experiment.

For any preimage-sampleable function `psf` that shares the deterministic image map (`eval`) and
shortness predicate (`isShort`) with the concrete Falcon PSF, the keyed GPV collision-finding
advantage equals the SIS advantage against `ntruPSFCollisionProblem`: both sample a key from
`hr.gen`, run the adversary, and accept on two distinct short preimages with equal image. Only the
trapdoor sampler differs between `psf` and `falconPSF`, and the collision experiment never invokes
it, so the equality holds for any such `psf`. This bridge turns the abstract GPV collision branch
into the Falcon NTRU-SIS hardness target. -/
theorem collisionFindingAdvantage_eq_ntruPSF
    (psf : PreimageSampleableFunction (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (hEval : ∀ pk x, psf.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, psf.isShort x = (falconPSF p prims).isShort x)
    (B : GPVHashAndSign.CollisionAdversary (PK := PublicKey p) (Domain := Rq p.n × Rq p.n)) :
    GPVHashAndSign.collisionFindingAdvantage psf hr B
      = SIS.advantage (ntruPSFCollisionProblem p prims hr) B := by
  simp only [GPVHashAndSign.collisionFindingAdvantage, GPVHashAndSign.collisionFindingExperiment,
    SIS.advantage, SIS.experiment, ntruPSFCollisionProblem, hEval, hShort, bind_assoc, pure_bind]

/-! ### Ideal-sampler min-entropy

The exact-match (programmed-preimage) term of the decomposed frontier is controlled by the
*guessing probability* of the ideal trapdoor sampler
(`GPVHashAndSign.programmedPreimageAdvantage_le_of_prEvent_trapdoorSample_le`).
`idealSamplerGuessBound` names the per-call pointwise-mass bound; it is discharged into the
collision-only headline by `euf_cma_collision_security`. -/

/-- **Per-call guessing-probability (min-entropy) bound for the ideal trapdoor sampler**: on
every honestly generated key pair and every hash target `c`, no single preimage carries more
than `εpp` of the ideal sampler's output mass — equivalently, the sampler has min-entropy at
least `log₂ (1/εpp)` at every honest key and target.

For the exact-arithmetic discrete Gaussian over the NTRU lattice coset, which GPV08 and [FGdG+25]
analyze and which `idealPSF` can only approximate, the literature value is `εpp = 2^(-H∞)` of the
coset Gaussian `D_{Λ+c,σ}`, and GPV08 Lemma 2.10 gives `H∞ ≥ n - 1` bits once `σ` exceeds the
smoothing parameter of the lattice, so `εpp` is negligible at Falcon parameters (`n = 512` /
`1024`). What is formalized is a bound before reduction modulo `q`:
`LatticeCrypto.Falcon.SamplerMinEntropy` bounds the pointwise mass of `Primitives.ffSampling`'s
output by the product over its `4 · 2^κ` leaf draws, since the merge steps are injective, and by
`(1 / (σ_min √(2π) - 1)) ^ (4 · 2^κ)` under a leaf envelope. On honest keys only short
preimages carry mass (`idealSamplerGuessBound_of_short`), and a short preimage determines the
lattice point modulo `q` except for representatives at distance at least `q - β`. A bound on the
mass of those far representatives, which would give a numeric `εpp` for the reduced output, is
not formalized. The only proved instance is the trivial `εpp = 1`
(`idealSamplerGuessBound_one`), since pointwise masses of any sampler are probabilities. -/
def idealSamplerGuessBound
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (εpp : ℝ≥0∞) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
    Pr{let y ← idealPSF.trapdoorSample pk sk c}[y = x] ≤ εpp

/-- The trivial witness for the guessing-probability bound: pointwise output masses of any
sampler never exceed one, so `εpp = 1` is always admissible. -/
theorem idealSamplerGuessBound_one
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n)) :
    idealSamplerGuessBound p hr idealPSF 1 :=
  fun _pk _sk _h _c _x => prEvent_le_one _

/-- **The guessing bound only needs the short preimages.** On honest keys `CorrectAt` puts every
output of the ideal sampler inside the short set, so a preimage that is not short has no output
mass at all; a pointwise bound on the short preimages therefore bounds every preimage. This is
the form a sampler min-entropy theorem delivers (the reduction of a lattice point modulo `q` is
injective only on short vectors), and it is all the exact-match branch consumes. -/
theorem idealSamplerGuessBound_of_short
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (εpp : ℝ≥0∞)
    (hShort : ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      idealPSF.isShort x = true → Pr{let y ← idealPSF.trapdoorSample pk sk c}[y = x] ≤ εpp) :
    idealSamplerGuessBound p hr idealPSF εpp := by
  intro pk sk hmem c x
  by_cases hx : x ∈ support (idealPSF.trapdoorSample pk sk c)
  · exact hShort pk sk hmem c x (hCorrect pk sk hmem c x hx).2
  · rw [prEvent_eq_zero_of_not_mem_support _ hx]
    exact zero_le

/-! ## Falcon's rejection loop: attempt-level sampler transport

Falcon's signer is a rejection loop: `Falcon.signAttempt` draws a trapdoor preimage and returns
it only when the norm check `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋` passes, retrying otherwise.  This section
prices the concrete-to-ideal sampler swap at that granularity.

The attempt-level frontier separates the two costs, following [FGdG+25] Theorem 1, which
accounts over `C_s` sampling calls *including* retries and carries the per-attempt acceptance
probability explicitly:

* `attemptTransport ε_step` — the gap between Falcon's attempt and an idealized attempt, both of
  which may reject, so the rejection rate does not enter `ε_step`;
* `attemptRejectBound pRej` — the idealized per-attempt rejection probability;
* `idealAttemptResamples` — the idealized attempt is a rejection sampler for the reject-free
  `idealPSF` that the GPV bounds consume (`ProbComp.ResamplesTo`).

`measureTVDist_falconRetryPSF_trapdoorSample_le` combines them into
`ε_step / (1 - pRej) + pRej ^ maxAttempts` — approximation error accumulated across retries plus
the attempt-budget exhaustion mass — and `euf_cma_security` carries that as
the sampler loss. -/

/-- **Falcon's rejection loop as a preimage-sampleable function.**  The norm-checked attempt
`Falcon.signAttempt` retried up to `maxAttempts` times at one target, read as a total
computation by `ProbComp.retryToDefault`, which returns `default` when every attempt rejects.
Inside `GPVHashAndSign` the target is the hash of one salt, so every retry reuses that salt;
`Falcon.sign` instead draws a fresh salt per retry.  The deterministic `eval` and `isShort`
components are those of `falconPSF`, so the collision and verification theory transfers
verbatim. -/
noncomputable def falconRetryPSF (maxAttempts : ℕ) :
    PreimageSampleableFunction (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n) where
  eval := (falconPSF p prims).eval
  trapdoorSample pk sk c := ProbComp.retryToDefault (signAttempt p prims pk sk c) maxAttempts
  isShort := (falconPSF p prims).isShort

/-- The Falcon signature scheme over the rejection-loop signer: the GPV hash-and-sign
construction at `falconRetryPSF`. -/
noncomputable def falconRetrySignatureAlg
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt]
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p)) :
    SignatureAlg (OracleComp (unifSpec + (Salt × List Byte →ₒ Rq p.n)))
      (M := List Byte) (PK := PublicKey p) (SK := SecretKey p)
      (S := Salt × (Rq p.n × Rq p.n)) :=
  GPVHashAndSign (falconRetryPSF p prims maxAttempts) hr (List Byte) Salt

/-- **Per-attempt sampler approximation.**  On honestly generated keys and at every hash
target, Falcon's rejection-sampling attempt and an idealized attempt are within
total-variation distance `ε_step` on the discrete σ-algebra of attempt outcomes.  Both sides may
reject, so the rejection rate itself does not enter `ε_step`; it is carried by
`attemptRejectBound`. -/
def attemptTransport
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (ε_step : ℝ) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c : Rq p.n,
    letI : MeasurableSpace (Option (Rq p.n × Rq p.n)) := ⊤
    measureTVDist (signAttempt p prims pk sk c) (idealAttempt pk sk c) ≤ ε_step

/-- **Per-attempt rejection probability of the idealized attempt.**  This is `1 - p` for the
acceptance probability `p` of [FGdG+25] Theorem 1. -/
def attemptRejectBound
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (pRej : ℝ) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c : Rq p.n,
    Pr{let x ← idealAttempt pk sk c}[x = none].toReal ≤ pRej

/-- **The idealized attempt is a rejection sampler for the ideal PSF.**  Replacing a rejection
by a fresh draw from `idealPSF.trapdoorSample` reproduces its law, so the accepted outputs of
the attempt are exactly the ideal sampler conditioned on acceptance. -/
def idealAttemptResamples
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n)) : Prop :=
  ∀ pk sk, (pk, sk) ∈ support hr.gen → ∀ c : Rq p.n,
    ProbComp.ResamplesTo (idealAttempt pk sk c) (idealPSF.trapdoorSample pk sk c)

/-- **The rejection loop transports at attempt granularity.**  Falcon's retry signer is within
`ε_step / (1 - pRej) + pRej ^ maxAttempts` of the reject-free ideal sampler: the per-attempt
precision gap accumulated geometrically across retries
(`ProbComp.measureTVDist_retryToDefault_le_div`), plus the attempt-budget exhaustion mass
(`ProbComp.measureTVDist_retryToDefault_le_pow`), on the discrete σ-algebra of preimages.

Neither summand contains the rejection probability as an additive term: `pRej` enters only through
the retry-count factor `1 / (1 - pRej)` and the exhaustion power `pRej ^ maxAttempts`. -/
theorem measureTVDist_falconRetryPSF_trapdoorSample_le
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (ε_step pRej : ℝ) (maxAttempts : ℕ)
    (hStep : attemptTransport p prims hr idealAttempt ε_step)
    (hRej : attemptRejectBound p hr idealAttempt pRej)
    (hRes : idealAttemptResamples p hr idealAttempt idealPSF)
    (hRej1 : pRej < 1)
    (pk : PublicKey p) (sk : SecretKey p) (hmem : (pk, sk) ∈ support hr.gen)
    (c : Rq p.n) :
    letI : MeasurableSpace (Rq p.n × Rq p.n) := ⊤
    measureTVDist ((falconRetryPSF p prims maxAttempts).trapdoorSample pk sk c)
        (idealPSF.trapdoorSample pk sk c)
      ≤ ε_step / (1 - pRej) + pRej ^ maxAttempts := by
  let : MeasurableSpace (Rq p.n × Rq p.n) := ⊤
  let : MeasurableSpace (Option (Rq p.n × Rq p.n)) := ⊤
  refine le_trans (measureTVDist_triangle _
    (ProbComp.retryToDefault (idealAttempt pk sk c) maxAttempts) _) (add_le_add ?_ ?_)
  · exact ProbComp.measureTVDist_retryToDefault_le_div _ _ (hStep pk sk hmem c)
      (hRej pk sk hmem c) hRej1 maxAttempts
  · exact ProbComp.measureTVDist_retryToDefault_le_pow _ _ (hRes pk sk hmem c)
      (hRej pk sk hmem c) maxAttempts

/-- **Conditional EUF-CMA bound for the idealized Falcon rejection-loop signer.** Conditional on
the sampler hypotheses, and not below one at Falcon's parameters with what is proved so far (see
*What the bounds give at Falcon's parameters* in the module docstring).

For any query-bounded adversary `A` against `falconRetrySignatureAlg`, the GPV reductions of `A`
with its final verification query appended (`appendForgeQuery`), at the domain sampler
`domainSample`, satisfy:

  `Adv^{EUF-CMA}(A) ≤ Adv^{collision}_{Falcon-PSF}(B_coll)`
  `    + (qSign + qHash + 1) · Adv^{exact-match}(B_exact)`
  `    + collisionBound Salt qSign (qHash + 1)`
  `    + qSign · (ε_step / (1 - pRej) + pRej ^ maxAttempts)`

- `B_coll` runs the ideal-scheme adversary with a simulated signing oracle and extracts two distinct
  short preimages of one programmed random-oracle value, with no `qHash` loss factor. It samples
  through `domainSample`, so this term is a hardness assumption only when `domainSample` needs no
  trapdoor.
- `B_exact` guesses one of the programmed entries and tries to reproduce the hidden short preimage
  there; its advantage is at most the ideal sampler's guessing probability, which
  `euf_cma_collision_security` uses in place of it.
- `collisionBound` is the salt birthday bound, a simplified form of the `Q_s · (C_s + Q_H) / 2^k`
  term of [FGdG+25] Theorem 1.
- The sampler loss is derived from the per-attempt gap `ε_step`, the idealized per-attempt rejection
  probability `pRej` and the attempt budget `maxAttempts`
  (`measureTVDist_falconRetryPSF_trapdoorSample_le`).

**The GPV laws `hCorrect` and `hReg`** are taken on the support of `hr.gen` only, through the
valid-key-restricted `GPVHashAndSign.euf_cma_split_bound_of_queryBound`. The universal forms are
unsatisfiable for the Falcon PSF: `isShort` is the norm bound `‖·‖₂² ≤ betaSquared`, `PublicKey` is
unconstrained, and a key with `h = 0` together with a large-norm target `c` has no short preimage.
-/
theorem euf_cma_security
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash maxAttempts : ℕ)
    (ε_step pRej : ℝ) (hε : 0 ≤ ε_step) (hRej0 : 0 ≤ pRej) (hRej1 : pRej < 1)
    (adv : SignatureAlg.UnforgeableAdversary
      (falconRetrySignatureAlg p prims Salt maxAttempts hr))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hEval : ∀ pk x, idealPSF.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (domainSample : PublicKey p → ProbComp (Rq p.n × Rq p.n))
    (hReg : ∀ pk sk, (pk, sk) ∈ support hr.gen →
        (do let s ← domainSample pk; pure (idealPSF.eval pk s, s)
            : ProbComp (Rq p.n × (Rq p.n × Rq p.n))) =ᵈ
          (do let c ← ($ᵗ (Rq p.n)); let s ← idealPSF.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Rq p.n × (Rq p.n × Rq p.n))))
    (hAttempt : attemptTransport p prims hr idealAttempt ε_step)
    (hRej : attemptRejectBound p hr idealAttempt pRej)
    (hRes : idealAttemptResamples p hr idealAttempt idealPSF)
    (hQ : ∀ pk, GPVHashAndSign.signHashQueryBound
      (M := List Byte) (Salt := Salt) (Range := Rq p.n)
      (S' := Salt × (Rq p.n × Rq p.n))
      (α := List Byte × (Salt × (Rq p.n × Rq p.n))) (oa := adv.main pk)
      (qSign := qSign) (qHash := qHash)) :
    SignatureAlg.unforgeableAdvantage
        (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) adv ≤
      SIS.advantage (ntruPSFCollisionProblem p prims hr)
          (GPVHashAndSign.reduction idealPSF hr (List Byte) Salt
            (GPVHashAndSign.appendForgeQuery idealPSF hr (List Byte) Salt ⟨adv.main⟩)
            domainSample) +
        ((qSign + (qHash + 1) : ℕ) : ENNReal) *
          GPVHashAndSign.programmedPreimageAdvantage idealPSF hr
            (GPVHashAndSign.programmedPreimageReduction idealPSF hr (List Byte) Salt
              (GPVHashAndSign.appendForgeQuery idealPSF hr (List Byte) Salt ⟨adv.main⟩)
              domainSample qSign (qHash + 1)) +
        GPVHashAndSign.collisionBound Salt qSign (qHash + 1) +
        ENNReal.ofReal (qSign * (ε_step / (1 - pRej) + pRej ^ maxAttempts)) := by
  have hsplit := GPVHashAndSign.euf_cma_split_bound_of_queryBound (psf := idealPSF) (hr := hr)
    (M := List Byte) (Salt := Salt) hCorrect domainSample hReg qSign qHash ⟨adv.main⟩ hQ
  rw [← collisionFindingAdvantage_eq_ntruPSF p prims idealPSF hr hEval hShort]
  have hlt : (0 : ℝ) < 1 - pRej := by linarith
  have hεtot : 0 ≤ ε_step / (1 - pRej) + pRej ^ maxAttempts :=
    add_nonneg (div_nonneg hε (le_of_lt hlt)) (pow_nonneg hRej0 maxAttempts)
  have hAdvLe :
      SignatureAlg.unforgeableAdvantage
          (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) adv ≤
        SignatureAlg.unforgeableAdvantage
            (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt)
            (⟨adv.main⟩ : SignatureAlg.UnforgeableAdversary
              (GPVHashAndSign idealPSF hr (List Byte) Salt)) +
          ENNReal.ofReal (qSign * (ε_step / (1 - pRej) + pRej ^ maxAttempts)) :=
    GPVHashAndSign.advantage_le_advantage_add_of_trapdoorSample_measureTVDist
      (falconRetryPSF p prims maxAttempts) idealPSF hr (List Byte) Salt
      (fun pk x => (hEval pk x).symm) (fun x => (hShort x).symm) hεtot
      (fun pk sk hmem c => measureTVDist_falconRetryPSF_trapdoorSample_le p prims hr
        idealAttempt idealPSF ε_step pRej maxAttempts hAttempt hRej hRes hRej1 pk sk hmem c)
      qSign adv (fun pk => (hQ pk).1)
  exact le_trans hAdvLe (by gcongr)

/-- **Collision-only EUF-CMA security of the Falcon rejection-loop signer.**
Conditional, and not below one at Falcon's parameters with what is proved so far: the only
guessing bound proved is `εpp = 1` (`idealSamplerGuessBound_one`), at which the exact-match
term is `qSign + qHash + 1`.
`euf_cma_security` with the exact-match branch discharged by the ideal
sampler's guessing-probability bound `hGuess`
(`GPVHashAndSign.programmedPreimageAdvantage_le_of_prEvent_trapdoorSample_le`). -/
theorem euf_cma_collision_security
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash maxAttempts : ℕ)
    (ε_step pRej : ℝ) (hε : 0 ≤ ε_step) (hRej0 : 0 ≤ pRej) (hRej1 : pRej < 1)
    (εpp : ℝ≥0∞)
    (adv : SignatureAlg.UnforgeableAdversary
      (falconRetrySignatureAlg p prims Salt maxAttempts hr))
    (idealAttempt : PublicKey p → SecretKey p → Rq p.n →
      ProbComp (Option (Rq p.n × Rq p.n)))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hEval : ∀ pk x, idealPSF.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (domainSample : PublicKey p → ProbComp (Rq p.n × Rq p.n))
    (hReg : ∀ pk sk, (pk, sk) ∈ support hr.gen →
        (do let s ← domainSample pk; pure (idealPSF.eval pk s, s)
            : ProbComp (Rq p.n × (Rq p.n × Rq p.n))) =ᵈ
          (do let c ← ($ᵗ (Rq p.n)); let s ← idealPSF.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Rq p.n × (Rq p.n × Rq p.n))))
    (hAttempt : attemptTransport p prims hr idealAttempt ε_step)
    (hRej : attemptRejectBound p hr idealAttempt pRej)
    (hRes : idealAttemptResamples p hr idealAttempt idealPSF)
    (hQ : ∀ pk, GPVHashAndSign.signHashQueryBound
      (M := List Byte) (Salt := Salt) (Range := Rq p.n)
      (S' := Salt × (Rq p.n × Rq p.n))
      (α := List Byte × (Salt × (Rq p.n × Rq p.n))) (oa := adv.main pk)
      (qSign := qSign) (qHash := qHash))
    (hGuess : idealSamplerGuessBound p hr idealPSF εpp) :
    SignatureAlg.unforgeableAdvantage
        (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) adv ≤
      SIS.advantage (ntruPSFCollisionProblem p prims hr)
          (GPVHashAndSign.reduction idealPSF hr (List Byte) Salt
            (GPVHashAndSign.appendForgeQuery idealPSF hr (List Byte) Salt ⟨adv.main⟩)
            domainSample) +
        ((qSign + (qHash + 1) : ℕ) : ENNReal) * εpp +
        GPVHashAndSign.collisionBound Salt qSign (qHash + 1) +
        ENNReal.ofReal (qSign * (ε_step / (1 - pRej) + pRej ^ maxAttempts)) := by
  refine le_trans (euf_cma_security p prims Salt hr qSign qHash maxAttempts ε_step pRej
    hε hRej0 hRej1 adv idealAttempt idealPSF hEval hShort hCorrect domainSample hReg
    hAttempt hRej hRes hQ) ?_
  gcongr
  exact GPVHashAndSign.programmedPreimageAdvantage_le_of_prEvent_trapdoorSample_le
    idealPSF hr _ hGuess

end Falcon
