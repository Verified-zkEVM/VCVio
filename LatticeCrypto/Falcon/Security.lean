/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/
import LatticeCrypto.Falcon.Scheme
import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Falcon Security

This file states the high-level security theorems for the Falcon signature scheme.

## Scope: an idealized Falcon/GPV model

The theorems here are about an **idealized Falcon model**, precisely:

- The scheme is `falconSignatureAlg` — the generic GPV hash-and-sign scheme
  (`GPVHashAndSign`) instantiated at the Falcon PSF. Signatures carry the full `(s₁, s₂)`
  preimage; the compressed `s₂`-only wire encoding and byte-level (de)serialization of
  FN-DSA are not modeled.
- Arithmetic is exact: the trapdoor sampler enters only through an ideal
  preimage-sampleable abstraction (`idealPSF` in `euf_cma_security`) sharing the
  deterministic `eval`/`isShort` of `falconPSF`. Floating-point `ffSampling` and its
  precision analysis are not modeled; the concrete-to-ideal sampler swap is the single
  `hTransport` hypothesis.
- Machine-checked verification correctness (`verify` accepting honest signatures) is not
  formalized here: it requires a retry-loop signer together with
  preimage-sampleable-function correctness (`s₁ + s₂ · h = c` on honest keys), the latter
  routing through the floating-point inverse-FFT rounding in `Falcon.fromFFTPreimage`.
- No cost model is attached: the reductions are constructed explicitly but their
  polynomial runtime is not machine-checked. They perform no exhaustive search and no
  noncomputable steps beyond the ambient probabilistic semantics.

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
`Falcon.advantage_le_ntruSISProblemKeyed` / `Falcon.euf_cma_security_ntruSIS` (advantage
level, at the honest key distribution `ntruSISProblemKeyed`) in
`LatticeCrypto.Falcon.SISBridge`; the remaining distance between the honest key
distribution and this problem's uniform challenge is a decisional-NTRU assumption. -/
noncomputable def ntruSISProblem [SampleableType (Rq p.n)] :
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
any transport bound `ε_sampler` on the concrete-to-ideal sampler swap (the
`hTransport` hypothesis), there exist:

- a collision reduction `B_coll` for the distinct-preimage branch,
- a programmed-preimage replay reduction `B_exact` for the exact-match branch,

such that:

  `Adv^{EUF-CMA}_{Falcon+}(A)`
  `  ≤ Adv^{collision}_{Falcon-PSF}(B_coll)`
  `    + (qSign + qHash) · Adv^{exact-match}_{Falcon-PSF}(B_exact)`
  `    + (qSign + qHash)² / (2 · |Salt|) + ε_sampler`

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

**Term 3: `(qSign + qHash)² / (2 · |Salt|)`.**
Salt collision probability over every salt appearing in a signing query or a
random-oracle query, bounded by the birthday paradox. This is a simplified form of the
`Q_s · (C_s + Q_H) / 2^k` term from [FGdG+25] Theorem 1.

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
4. Account for finite precision via the `hTransport` sampler-transport hypothesis.

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
    -- adversary. Assumed here as a single transport hypothesis; decomposing it into a
    -- per-call sampler-approximation bound with a proven adaptive accumulation is the
    -- intended refinement.
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
