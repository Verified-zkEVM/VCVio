/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/
import LatticeCrypto.Falcon.Correctness
import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
import VCVio.EvalDist.RenyiDivergence
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Falcon Security

This file states the high-level security theorems and hardness assumptions for the
Falcon signature scheme. Abstract signing correctness is proved in
`LatticeCrypto.Falcon.Correctness`.

## EUF-CMA Security

The main security theorem reduces EUF-CMA to a Falcon-PSF collision problem sampled
from the same key distribution as the scheme. The precise
bound follows [FGdG+25] Theorem 1 (first concrete proof for Falcon+), refined by
[Jia+26] (basis-specific Rényi analysis that eliminates the 7-bit security loss).

### The exact theorem ([FGdG+25] Theorem 1, adapted)

For adversary `A` making `Q_s` signing queries and `Q_H` RO queries, with at most
`C_s` total preimage sampling calls (including retries):

  `Adv^{UF-CMA}_{Falcon+}(A)`
  `  ≤ (r_u^{C_s} · (r_p^{C_s} · Adv^{ISIS}(B))^{…})^{…}`
  `  + Σ C(C_s,i) · (1-p)^{C_s-i} · p^i`
  `  + Q_s · (C_s + Q_H) / 2^k`

where:
- `r_p = R_{a_p}(PreSmp ‖ D_{Λ,s,c})`: sampler Rényi divergence
- `r_u = R_{a_u}(U(R_q) ‖ Q_h)`: RO simulation Rényi divergence
- `p = Pr[‖(s₁,s₂)‖ ≤ β]`: acceptance probability per attempt
- `k = 320`: salt bits
- `a_p, a_u > 1`: Rényi orders (optimized per instance)

### Concrete security levels ([Jia+26] Table 6)

Using basis-specific analysis (Theorems 2–4 of [Jia+26]):

| Scheme | `loss_p` | `loss_u` | Bit security |
|---|---|---|---|
| Falcon+-512 | 0.093 bits | 0.093 bits | 119.81 |
| Falcon+-1024 | 0.087 bits | 0.087 bits | 277.82 (256 limited by salt term) |

The `loss_p` and `loss_u` are *maximum* over 1000 random Falcon bases ([Jia+26]
Table 5), replacing the worst-case 3.29/3.14 bits from [FGdG+25].

### Sampler precision requirements

The sampler Rényi divergence `r_p` depends on floating-point precision via:
  `δ_{RE}(PreSmp, D_{Λ,s,c}) ≤ δ_{B,s} = ∏_{i=1}^{2n} (1+ε_i)/(1-ε_i) - 1`
where `ε_i = ε^{α_i²}` and `α_i = ‖B‖_{GS}/‖b̃_i‖` ([Jia+26] Theorem 2).

The required precision `δ_c + δ_σ` for provable security:
- Required by proof: `≤ 2^{-46}` (for `λ = 256`, `Q_s = 2^{64}`)
- binary64 (53-bit): achieves only `2^{-37}` worst case ([TWFalcon]),
  provably secure for only `2^{47}` queries
- Triple-word (72-bit): achieves `2^{-57}`, fully sufficient
- Exact (infinite precision): `r_p = 1` (no loss)

### Salt collision

The salt collision term `Q_s · (C_s + Q_H) / 2^k` from [FGdG+25] Theorem 1 is slightly
tighter than the birthday bound `Q_s² / (2 · 2^k)` from GPV08 Proposition 6.2.
For `k = 320`, both are negligible.

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


open OracleComp OracleSpec ENNReal

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ### NTRU-SIS Hardness Assumptions -/

/-- A parameterized NTRU-SIS problem: given `h ∈ R_q`, find short
`(s₁, s₂) ∈ R_q²` satisfying `s₁ + s₂ · h = 0 mod q` with
`‖(s₁, s₂)‖₂² ≤ bound`.

The challenge sampler is explicit because Falcon uses both the idealized uniform-`h`
problem and the key-distributed `h` problem induced by actual key generation. -/
noncomputable def ntruSISProblemWithSample (sampleH : ProbComp (Rq p.n)) (bound : ℕ) :
    SIS.Problem (Rq p.n) (Rq p.n × Rq p.n) where
  sampleChallenge := sampleH
  isValid h x :=
    decide (x ≠ (0, 0)) &&
    decide (pairL2NormSq x.1 x.2 ≤ bound) &&
    decide (x.1 + negacyclicMul x.2 h = 0)

/-- The idealized NTRU-SIS problem: given uniform `h ∈ R_q` (the Falcon public key),
find short `(s₁, s₂) ∈ R_q²` satisfying `s₁ + s₂ · h = 0 mod q` with
`‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`.

This is the lattice problem underlying Falcon's security. It is an instance of
the generic SIS problem where the matrix is the single-row matrix `[I | h]`
over the cyclotomic ring `R_q = ℤ_q[x]/(x^n + 1)`. -/
noncomputable def ntruSISProblem [SampleableType (Rq p.n)] :
    SIS.Problem (Rq p.n) (Rq p.n × Rq p.n) :=
  ntruSISProblemWithSample p ($ᵗ (Rq p.n)) p.betaSquared

/-- The key-distributed NTRU-SIS problem induced by a Falcon key generator relation.

The challenge is `pk.h` for `(pk, sk)` sampled by `hr.gen`, not a uniformly sampled
ring element. This is the direct target obtained from a Falcon PSF collision before
adding a separate decisional/uniformity step for the public-key distribution. -/
noncomputable def ntruKeyedSISProblem
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (bound : ℕ) : SIS.Problem (Rq p.n) (Rq p.n × Rq p.n) where
  sampleChallenge := do
    let (pk, _) ← hr.gen
    pure pk.h
  isValid h x :=
    decide (x ≠ (0, 0)) &&
    decide (pairL2NormSq x.1 x.2 ≤ bound) &&
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

/-- The kernel vector obtained from a collision pair. -/
def collisionToNTRUSISSolution
    (xs : (Rq p.n × Rq p.n) × (Rq p.n × Rq p.n)) : Rq p.n × Rq p.n :=
  (xs.1.1 - xs.2.1, xs.1.2 - xs.2.2)

/-- Turn a Falcon-PSF collision adversary into a keyed NTRU-SIS adversary with
the `4 * betaSquared` norm bound.

The adversary only receives `h`; this is enough to reconstruct `PublicKey`, whose only
field is `h`, and then difference the two collision preimages. -/
noncomputable def ntruPSFCollisionToKeyedSISAdversary
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (adv : SIS.Adversary (ntruPSFCollisionProblem p prims hr)) :
    SIS.Adversary (ntruKeyedSISProblem p hr (4 * p.betaSquared)) :=
  fun h => do
    let xs ← adv ⟨h⟩
    pure (collisionToNTRUSISSolution p xs)

private theorem negacyclicMul_sub_left {n : ℕ} (a b c : Rq n) :
    negacyclicMul (a - b) c = negacyclicMul a c - negacyclicMul b c := by
  calc
    negacyclicMul (a - b) c = negacyclicMul c (a - b) := by
      simpa [negacyclicMul] using LatticeCrypto.vectorRing_mul_comm (a - b) c
    _ = negacyclicMul c a - negacyclicMul c b := by
      simpa [negacyclicMul] using LatticeCrypto.vectorRing_mul_sub_right c a b
    _ = negacyclicMul a c - negacyclicMul b c := by
      have hca : negacyclicMul c a = negacyclicMul a c := by
        simpa [negacyclicMul] using LatticeCrypto.vectorRing_mul_comm c a
      have hcb : negacyclicMul c b = negacyclicMul b c := by
        simpa [negacyclicMul] using LatticeCrypto.vectorRing_mul_comm c b
      rw [hca, hcb]

/-- A valid Falcon-PSF collision yields a valid solution to the key-distributed
NTRU-SIS problem at bound `4 * betaSquared`.

The algebraic kernel equation comes from subtracting the equal PSF images. The norm
bound is the centered-residue `ℓ₂` triangle inequality: if both preimages are
`betaSquared`-short, then their difference has squared norm at most `4 * betaSquared`. -/
theorem ntruPSFCollision_to_keyedSIS_valid
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (pk : PublicKey p) (xs : (Rq p.n × Rq p.n) × (Rq p.n × Rq p.n))
    (hvalid : (ntruPSFCollisionProblem p prims hr).isValid pk xs = true) :
    (ntruKeyedSISProblem p hr (4 * p.betaSquared)).isValid pk.h
      (collisionToNTRUSISSolution p xs) = true := by
  rcases xs with ⟨x, y⟩
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [ntruPSFCollisionProblem, falconPSF, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  rcases hvalid with ⟨⟨⟨hne, heval⟩, hxshort⟩, hyshort⟩
  simp only [ntruKeyedSISProblem, collisionToNTRUSISSolution, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · constructor
    · intro hzero
      apply hne
      simp only [Prod.mk.injEq] at hzero ⊢
      have sub_eq_zero_poly {a b : Rq p.n} (h : a - b = 0) : a = b := by
        ext i
        have hi := congrArg (fun z : Rq p.n => (coeffRing p.n).backend.coeff z i) h
        simp only [LatticeCrypto.NegacyclicRing.coeff_sub,
          LatticeCrypto.NegacyclicRing.coeff_zero] at hi
        exact sub_eq_zero.mp hi
      exact ⟨sub_eq_zero_poly hzero.1, sub_eq_zero_poly hzero.2⟩
    · have hnorm :=
        LatticeCrypto.pairL2NormSq_sub_le_two_mul_add
          (q := modulus) (n := p.n) (x₁, x₂) (y₁, y₂)
      have hnorm' :
          LatticeCrypto.pairL2NormSq (x₁ - y₁) (x₂ - y₂) ≤
            2 * (LatticeCrypto.pairL2NormSq x₁ x₂ +
              LatticeCrypto.pairL2NormSq y₁ y₂) := by
        simpa using hnorm
      change LatticeCrypto.pairL2NormSq (x₁ - y₁) (x₂ - y₂) ≤ 4 * p.betaSquared
      change LatticeCrypto.pairL2NormSq x₁ x₂ ≤ p.betaSquared at hxshort
      change LatticeCrypto.pairL2NormSq y₁ y₂ ≤ p.betaSquared at hyshort
      nlinarith
  · rw [negacyclicMul_sub_left]
    ext i
    have hcoeff := congrArg (fun z : Rq p.n => (coeffRing p.n).backend.coeff z i) heval
    simp only [LatticeCrypto.NegacyclicRing.coeff_add,
      LatticeCrypto.NegacyclicRing.coeff_sub, LatticeCrypto.NegacyclicRing.coeff_zero] at hcoeff ⊢
    have hsub :
        (coeffRing p.n).backend.coeff x₁ i +
            (coeffRing p.n).backend.coeff (negacyclicMul x₂ pk.h) i -
          ((coeffRing p.n).backend.coeff y₁ i +
            (coeffRing p.n).backend.coeff (negacyclicMul y₂ pk.h) i) = 0 :=
      sub_eq_zero.mpr hcoeff
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub

/-- Advantage bridge: the keyed NTRU-SIS adversary built from a Falcon-PSF collision adversary
wins with at least the collision adversary's advantage.

Both experiments draw the key pair from `hr.gen` and run the *same* collision adversary on the
*same* public key (`⟨pk.h⟩ = pk`, as `PublicKey` has a single field); the keyed experiment then
differences the output. Every valid collision differences to a valid keyed-SIS solution
(`ntruPSFCollision_to_keyedSIS_valid`), so the keyed win event contains the collision win event
pointwise, giving the inequality. -/
theorem ntruPSFCollision_advantage_le_keyedSIS
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (collisionReduction : SIS.Adversary (ntruPSFCollisionProblem p prims hr)) :
    SIS.advantage (ntruPSFCollisionProblem p prims hr) collisionReduction ≤
      SIS.advantage (ntruKeyedSISProblem p hr (4 * p.betaSquared))
        (ntruPSFCollisionToKeyedSISAdversary p prims hr collisionReduction) := by
  unfold SIS.advantage SIS.experiment
  -- Unfold only the challenge samplers and the reduction adversary, keeping `isValid` folded.
  have hsc_c : (ntruPSFCollisionProblem p prims hr).sampleChallenge
      = (hr.gen >>= fun x => pure x.1) := rfl
  have hsc_k : (ntruKeyedSISProblem p hr (4 * p.betaSquared)).sampleChallenge
      = (hr.gen >>= fun x => pure x.1.h) := rfl
  rw [hsc_c, hsc_k]
  simp only [ntruPSFCollisionToKeyedSISAdversary, bind_assoc, pure_bind]
  -- Common prefix `hr.gen >>= collisionReduction`; `⟨x.1.h⟩ = x.1` by structure eta.
  refine probOutput_bind_mono fun x _hx => ?_
  refine probOutput_bind_mono fun xs _hxs => ?_
  by_cases hC : (ntruPSFCollisionProblem p prims hr).isValid x.1 xs = true
  · have hK := ntruPSFCollision_to_keyedSIS_valid p prims hr x.1 xs hC
    rw [hC, hK]
  · rw [Bool.not_eq_true] at hC
    rw [hC, probOutput_pure]
    simp

/-! ### Sampler Quality Hypotheses -/

/-- The trapdoor sampler quality hypothesis: the Rényi divergence of order `a > 1`
between the concrete trapdoor sampler and an ideal sampler is bounded by `R`.

This captures the floating-point precision loss in `ffSampling` and `SamplerZ`.
The structure separates the *existence* of the bound from its *concrete value*.

### Precise bound ([Jia+26] Corollary 1, refining [Pre17] Lemma 6)

For basis `B` with Gram-Schmidt vectors `b̃_i`, let `α_i = ‖B‖_{GS} / ‖b̃_i‖` and
`ε_i = ε^{α_i²}` where `ε` is the global closeness parameter. Then:

  `R_a(PreSmp(B,s,t) ‖ D_{Λ(B),s,t}) ≲ 1 + a · δ²_{B,s} / 2`

where `δ_{B,s} = ∏_i (1+ε_i)/(1-ε_i) - 1` is the basis-specific relative error.

The previous worst-case analysis ([Pre17]) used `δ ≈ 4nε`, but the basis-specific
metric gives `δ_{B,s} ≈ 4nε / (0.87 · |ln ε|)`, which is ~21× tighter for Falcon
parameters ([Jia+26] Section 4.3).

### Optimal Rényi order ([FGdG+25] Lemma 4)

The Rényi orders `a_p, a_u` should be chosen to minimize the total security loss
`C_s · log₂(r_p) + C_s · log₂(r_u) + λ/a`, which gives much larger optimal orders
than the traditional `a = 2λ`:

| | [FGdG+25] | [Jia+26] |
|---|---|---|
| Falcon+-512 `a_p` | 72.96 | 2577.30 |
| Falcon+-512 `a_u` | 69.64 | 2573.91 |
| Falcon+-1024 `a_p` | 157.05 | 6417.73 |
| Falcon+-1024 `a_u` | 153.28 | 6413.92 |

### Precision requirements ([TWFalcon] Section 3)

The combined FP error must satisfy `10·√(2n)·(δ_c + δ_σ) ≤ 2^{-37}` for the
Rényi argument to hold with `λ = 256`, `Q_s = 2^{64}`. This requires
`δ_c + δ_σ ≤ 2^{-46}`. Measured precision:

| Arithmetic | `δ_c + δ_σ` | Provably secure queries |
|---|---|---|
| binary64 (53-bit) | ≤ 2^{-37} (worst) | 2^{47} |
| triple-word (72-bit) | ≤ 2^{-57} | 2^{68} (exceeds 2^{64}) |
| exact | 0 | ∞ |

Discharging this hypothesis requires composing per-operation FPR error bounds
(from `ApproxArith.lean` / `FPRBridge.lean`) through the `ffSampling` recursion. -/
structure SamplerQuality (pk : PublicKey p) (sk : SecretKey p) where
  /-- The Rényi divergence order. Optimal values are much larger than `2λ`:
  ~2577 for Falcon+-512, ~6418 for Falcon+-1024 ([Jia+26] Table 6). -/
  renyiOrder : ℝ
  hOrder : 1 < renyiOrder
  /-- The Rényi divergence bound `R ≥ 1`.
  By [Jia+26] Corollary 1: `R ≲ 1 + a · δ²_{B,s} / 2` where `δ_{B,s}` is the
  basis-specific relative error. For typical Falcon bases, `log₂ R < 2^{-10}`. -/
  bound : ℝ≥0∞
  /-- The ideal sampler: exact discrete Gaussian `D_{Λ^⊥, σ, c}` over the NTRU lattice
  coset. This is the target distribution that `ffSampling` approximates. -/
  idealSampler : Rq p.n → ProbComp (Rq p.n × Rq p.n)
  /-- Rényi divergence bound: for every target `c`, the Rényi divergence of order `a`
  between the concrete sampler and the ideal Gaussian is at most `R`. -/
  quality : ∀ c : Rq p.n,
    renyiDiv renyiOrder ((falconPSF p prims).trapdoorSample pk sk c) (idealSampler c) ≤ bound
  /-- Ideal sampler correctness: the ideal Gaussian always produces valid short preimages.
  This follows from the lattice geometry when `σ ≥ η_ε(Λ^⊥) · ‖B̃‖_GS`. -/
  idealCorrect : ∀ c : Rq p.n,
    ∀ x ∈ support (idealSampler c),
      (falconPSF p prims).eval pk x = c ∧ (falconPSF p prims).isShort x = true

/-- A concrete upper bound on the finite-precision sampler loss that is uniform over
all valid Falcon key pairs. This keeps the theorem statement non-vacuous while still
letting later work plug in sharper bounds from `SamplerQuality`. -/
def HasUniformSamplerLoss (samplerLoss : ENNReal) : Prop :=
  ∀ pk sk, validKeyPair p pk sk = true →
    ∃ quality : SamplerQuality p prims pk sk, quality.bound ≤ samplerLoss

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
    [SampleableType (Rq p.n)]
    (psf : PreimageSampleableFunction (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p))
    (hEval : ∀ pk x, psf.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, psf.isShort x = (falconPSF p prims).isShort x)
    (B : GPVHashAndSign.CollisionAdversary (PK := PublicKey p) (Domain := Rq p.n × Rq p.n)) :
    GPVHashAndSign.collisionFindingAdvantage psf hr B
      = SIS.advantage (ntruPSFCollisionProblem p prims hr) B := by
  simp only [GPVHashAndSign.collisionFindingAdvantage, GPVHashAndSign.collisionFindingExp,
    SIS.advantage, SIS.experiment, ntruPSFCollisionProblem, hEval, hShort, bind_assoc, pure_bind]

/-- **EUF-CMA security of Falcon** ([FGdG+25] Theorem 1 + [Jia+26] refined bounds),
generic in the salt type `Salt`.

For any EUF-CMA adversary `A` making at most `qSign` signing queries and `qHash`
random-oracle queries against the Falcon+ signature scheme with salt type `Salt`, and
any externally supplied bound `ε_sampler` that upper-bounds `SamplerQuality.bound` for
every valid Falcon key pair, there exist:

- a collision reduction `B_coll` for the distinct-preimage branch,
- a programmed-preimage replay reduction `B_exact` for the exact-match branch,

such that:

  `Adv^{EUF-CMA}_{Falcon+}(A)`
  `  ≤ Adv^{collision}_{Falcon-PSF}(B_coll)`
  `    + (qSign + qHash) · Adv^{exact-match}_{Falcon-PSF}(B_exact)`
  `    + qSign² / (2 · |Salt|) + ε_sampler`

### Error terms

**Term 1: `Adv^{collision}_{Falcon-PSF}(B)`.**
The GPV reduction is tight on the distinct-preimage branch: `B` runs `A` internally with
a simulated signing oracle (sign-then-hash strategy) and extracts two distinct short
Falcon preimages for the same programmed random-oracle value. There is no `Q_hash` loss
factor in this collision-style target.

**Term 2: `(qSign + qHash) · Adv^{exact-match}_{Falcon-PSF}(B_exact)`.**
The explicit multi-target loss for the exact-match branch. The reduction guesses one of
the programmed random-oracle entries and tries to show that reproducing the simulator's
hidden short preimage there is hard.

**Term 3: `qSign² / (2 · |Salt|)`.**
Salt collision probability, bounded by the birthday paradox. This is a simplified form
of the `Q_s · (C_s + Q_H) / 2^k` term from [FGdG+25] Theorem 1.

**Term 4: `ε_sampler`.**
The Rényi divergence-based sampler loss. The full [FGdG+25] bound has the structure
`r_u^{C_s} · (r_p^{C_s} · Adv^{ISIS})^{...}`, where `r_p` and `r_u` are the per-query
Rényi divergences for the sampler and RO simulation respectively.
[Jia+26] Theorems 2-4 show that with basis-specific analysis, the total loss
`C_s · (log r_p + log r_u)` is < 0.2 bits for all tested Falcon instances.
With exact arithmetic (infinite precision), `r_p = 1` and the sampler loss vanishes.

### Proof structure

1. The generic GPV split bound (`GPVHashAndSign.euf_cma_split_bound`) which reduces EUF-CMA to
   a collision branch, an exact-match replay branch with explicit factor `qSign + qHash`,
   and a birthday collision term.
2. Reinterpret the collision branch as an adversary for the Falcon PSF collision problem
   sampled from the same key distribution (`collisionFindingAdvantage_eq_ntruPSF`).
3. Leave the exact-match branch explicit in the theorem statement until it is discharged by
   a Falcon-specific min-entropy / one-way lemma.
4. Account for finite-precision via the sampler quality hypothesis.

**On the GPV laws (`hCorrect`/`hReg`/`hNeverFail`).** These are taken on the support of `hr.gen`
(honestly generated keys) only, via the valid-key-restricted `GPVHashAndSign.euf_cma_split_bound`.
The universal forms would be *unsatisfiable* for the Falcon PSF — `isShort` is the norm bound
`‖·‖₂² ≤ betaSquared`, `PublicKey` is unconstrained, and a key with `h = 0` together with a
large-norm target `c` (`‖c‖² > betaSquared`) has no short preimage — so no sampler could be both
correct and total at *every* key. Restricting to `support hr.gen` (where the NTRU geometry of a
valid key guarantees short preimages — the honest-key regime in which Falcon signatures verify)
makes the hypotheses satisfiable, so this theorem is conditional, not vacuous. The ideal sampler
`idealPSF` shares the deterministic `eval`/`isShort` of `falconPSF` (`hEval`/`hShort`); `hTransport`
carries the finite-precision concrete→ideal gap as the [FGdG+25] Rényi term `samplerLoss`, assumed
here in the
same way MLWE/SIS hardness is assumed. The collision branch is discharged by
`collisionFindingAdvantage_eq_ntruPSF`. -/
theorem euf_cma_security
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    [SampleableType (Rq p.n)] [Inhabited (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash : ℕ)
    (samplerLoss : ENNReal)
    (adv : SignatureAlg.unforgeableAdv
      (falconSignatureAlg p prims Salt hr))
    -- Ideal preimage-sampleable abstraction (truncated discrete Gaussian over the NTRU coset):
    -- same deterministic `eval`/`isShort` as `falconPSF`, GPV laws on honest keys only.
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hEval : ∀ pk x, idealPSF.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (hReg : ∃ domainSample : PublicKey p → ProbComp (Rq p.n × Rq p.n),
      ∀ pk sk, (pk, sk) ∈ support hr.gen →
        𝒟[(do let s ← domainSample pk; pure (idealPSF.eval pk s, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))] =
        𝒟[(do let c ← ($ᵗ (Rq p.n)); let s ← idealPSF.trapdoorSample pk sk c; pure (c, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))])
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support hr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    -- Finite-precision sampler transport ([FGdG+25] Rényi term): swapping the concrete signing
    -- oracle for the ideal one costs at most `samplerLoss` and yields a well-behaved ideal-scheme
    -- adversary. Derivable from `SamplerQuality`/`renyiDiv`; assumed here.
    (hTransport : ∃ adv' : SignatureAlg.unforgeableAdv
        (GPVHashAndSign idealPSF hr (List Byte) Salt),
      adv.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) ≤
          adv'.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) +
            samplerLoss ∧
        (∀ ds, GPVHashAndSign.ForgesQueriedPoint idealPSF hr (List Byte) Salt adv' ds) ∧
        (∀ pk, GPVHashAndSign.signHashQueryBound
          (M := List Byte) (Salt := Salt) (Range := Rq p.n)
          (S' := Salt × (Rq p.n × Rq p.n))
          (α := List Byte × (Salt × (Rq p.n × Rq p.n))) (oa := adv'.main pk)
          (qSign := qSign) (qHash := qHash))) :
    ∃ (collisionReduction : SIS.Adversary (ntruPSFCollisionProblem p prims hr))
      (exactMatchReduction : GPVHashAndSign.ProgrammedPreimageAdversary
        (PK := PublicKey p) (Domain := Rq p.n × Rq p.n) (Range := Rq p.n)),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) Salt) ≤
        SIS.advantage (ntruPSFCollisionProblem p prims hr) collisionReduction +
        ((qSign + qHash : ℕ) : ENNReal) *
          GPVHashAndSign.programmedPreimageAdvantage
            idealPSF hr exactMatchReduction +
        GPVHashAndSign.collisionBound Salt qSign qHash +
        samplerLoss := by
  obtain ⟨adv', hAdvLe, hForge', hQ'⟩ := hTransport
  obtain ⟨cRed, eRed, hsplit⟩ :=
    GPVHashAndSign.euf_cma_split_bound (psf := idealPSF) (hr := hr)
      (M := List Byte) (Salt := Salt) hCorrect hReg qSign qHash adv'
      hNeverFail hForge' hQ'
  refine ⟨cRed, eRed, ?_⟩
  have hbridge :
      GPVHashAndSign.collisionFindingAdvantage idealPSF hr cRed
        = SIS.advantage (ntruPSFCollisionProblem p prims hr) cRed :=
    collisionFindingAdvantage_eq_ntruPSF p prims idealPSF hr hEval hShort cRed
  rw [← hbridge]
  exact le_trans hAdvLe (by gcongr)

/-- EUF-CMA security expressed against the **key-distributed NTRU-SIS** problem (norm bound
`4 · betaSquared`), obtained by composing `euf_cma_security` with the collision→keyed-SIS
advantage bridge `ntruPSFCollision_advantage_le_keyedSIS`.

The reduction now terminates at `ntruKeyedSISProblem` — finding a short nonzero kernel vector for
the Falcon public key's `[I | h]` lattice — the standard lattice target, at the `4 · betaSquared`
bound that a difference of two `β`-short preimages achieves. The bound is otherwise identical to
`euf_cma_security` (only the first summand is replaced, using that the keyed adversary wins
whenever the collision adversary does). -/
theorem euf_cma_security_ntruSIS
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] [Nonempty Salt]
    [SampleableType (Rq p.n)] [Inhabited (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash : ℕ)
    (samplerLoss : ENNReal)
    (adv : SignatureAlg.unforgeableAdv
      (falconSignatureAlg p prims Salt hr))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hEval : ∀ pk x, idealPSF.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (hReg : ∃ domainSample : PublicKey p → ProbComp (Rq p.n × Rq p.n),
      ∀ pk sk, (pk, sk) ∈ support hr.gen →
        𝒟[(do let s ← domainSample pk; pure (idealPSF.eval pk s, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))] =
        𝒟[(do let c ← ($ᵗ (Rq p.n)); let s ← idealPSF.trapdoorSample pk sk c; pure (c, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))])
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support hr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    (hTransport : ∃ adv' : SignatureAlg.unforgeableAdv
        (GPVHashAndSign idealPSF hr (List Byte) Salt),
      adv.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) ≤
          adv'.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) Salt) +
            samplerLoss ∧
        (∀ ds, GPVHashAndSign.ForgesQueriedPoint idealPSF hr (List Byte) Salt adv' ds) ∧
        (∀ pk, GPVHashAndSign.signHashQueryBound
          (M := List Byte) (Salt := Salt) (Range := Rq p.n)
          (S' := Salt × (Rq p.n × Rq p.n))
          (α := List Byte × (Salt × (Rq p.n × Rq p.n))) (oa := adv'.main pk)
          (qSign := qSign) (qHash := qHash))) :
    ∃ (keyedReduction : SIS.Adversary (ntruKeyedSISProblem p hr (4 * p.betaSquared)))
      (exactMatchReduction : GPVHashAndSign.ProgrammedPreimageAdversary
        (PK := PublicKey p) (Domain := Rq p.n × Rq p.n) (Range := Rq p.n)),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) Salt) ≤
        SIS.advantage (ntruKeyedSISProblem p hr (4 * p.betaSquared)) keyedReduction +
        ((qSign + qHash : ℕ) : ENNReal) *
          GPVHashAndSign.programmedPreimageAdvantage
            idealPSF hr exactMatchReduction +
        GPVHashAndSign.collisionBound Salt qSign qHash +
        samplerLoss := by
  obtain ⟨cRed, eRed, hbound⟩ :=
    euf_cma_security p prims Salt hr qSign qHash samplerLoss adv idealPSF
      hEval hShort hCorrect hReg hNeverFail hTransport
  refine ⟨ntruPSFCollisionToKeyedSISAdversary p prims hr cRed, eRed, ?_⟩
  refine le_trans hbound ?_
  gcongr
  exact ntruPSFCollision_advantage_le_keyedSIS p prims hr cRed

/-- Concrete instantiation of `euf_cma_security` with the Falcon-specified 40-byte
(320-bit) salt.

The collision term specializes to `(qSign + qHash)² / (2 · 2^320)`. For the Falcon-specified
maximum of `qSign, qHash ≤ 2^64`, this is `≤ 2^{-191}`. -/
theorem euf_cma_security_bytes40
    [SampleableType (Rq p.n)] [Inhabited (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p))
    (qSign qHash : ℕ)
    (samplerLoss : ENNReal)
    (adv : SignatureAlg.unforgeableAdv
      (falconSignatureAlg p prims (Bytes 40) hr))
    (idealPSF : PreimageSampleableFunction
      (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n))
    (hEval : ∀ pk x, idealPSF.eval pk x = (falconPSF p prims).eval pk x)
    (hShort : ∀ x, idealPSF.isShort x = (falconPSF p prims).isShort x)
    (hCorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → idealPSF.CorrectAt pk sk)
    (hReg : ∃ domainSample : PublicKey p → ProbComp (Rq p.n × Rq p.n),
      ∀ pk sk, (pk, sk) ∈ support hr.gen →
        𝒟[(do let s ← domainSample pk; pure (idealPSF.eval pk s, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))] =
        𝒟[(do let c ← ($ᵗ (Rq p.n)); let s ← idealPSF.trapdoorSample pk sk c; pure (c, s)
              : ProbComp (Rq p.n × (Rq p.n × Rq p.n)))])
    (hNeverFail : ∀ pk sk, (pk, sk) ∈ support hr.gen →
      ∀ c, NeverFail (idealPSF.trapdoorSample pk sk c))
    (hTransport : ∃ adv' : SignatureAlg.unforgeableAdv
        (GPVHashAndSign idealPSF hr (List Byte) (Bytes 40)),
      adv.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) (Bytes 40)) ≤
          adv'.advantage (GPVHashAndSign.runtime (Range := Rq p.n) (List Byte) (Bytes 40)) +
            samplerLoss ∧
        (∀ ds, GPVHashAndSign.ForgesQueriedPoint idealPSF hr (List Byte) (Bytes 40) adv' ds) ∧
        (∀ pk, GPVHashAndSign.signHashQueryBound
          (M := List Byte) (Salt := Bytes 40) (Range := Rq p.n)
          (S' := Bytes 40 × (Rq p.n × Rq p.n))
          (α := List Byte × (Bytes 40 × (Rq p.n × Rq p.n))) (oa := adv'.main pk)
          (qSign := qSign) (qHash := qHash))) :
    ∃ (collisionReduction : SIS.Adversary (ntruPSFCollisionProblem p prims hr))
      (exactMatchReduction : GPVHashAndSign.ProgrammedPreimageAdversary
        (PK := PublicKey p) (Domain := Rq p.n × Rq p.n) (Range := Rq p.n)),
      adv.advantage
          (GPVHashAndSign.runtime
            (Range := Rq p.n) (List Byte) (Bytes 40)) ≤
        SIS.advantage (ntruPSFCollisionProblem p prims hr) collisionReduction +
        ((qSign + qHash : ℕ) : ENNReal) *
          GPVHashAndSign.programmedPreimageAdvantage
            idealPSF hr exactMatchReduction +
        GPVHashAndSign.collisionBound (Bytes 40) qSign qHash +
        samplerLoss :=
  euf_cma_security p prims (Bytes 40) hr qSign qHash samplerLoss adv
    idealPSF hEval hShort hCorrect hReg hNeverFail hTransport

end Falcon
