/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.MLDSA.SecurityNMA
public import LatticeCrypto.MLDSA.SecurityHVZK
public import VCVio.CryptoFoundations.Asymptotics.Negligible
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# ML-DSA EUF-NMA and EUF-CMA headlines

The composed security statements over the reductions of `LatticeCrypto.MLDSA.SecurityNMA`.
`nma_security_short` and `nma_security_fips` bound the EUF-NMA advantage of the short-key and
seed-derived schemes by MLWE and SelfTargetMSIS advantages; `nma_security_short_matrix` lands
the MLWE leg on the uniform-matrix problem `NMA.mldsaMatrixMLWE`.

`euf_cma_security_of_nma_short` composes the CMA-to-NMA engine with the short-model NMA leg; its
HVZK hypothesis is an open obligation (no witness below `ζ_zk = 1`, see its docstring).
`euf_cma_security_of_nma_fips` composes the same engine with the seed-model NMA leg
`nma_security_fips`, and `euf_cma_security_of_nma_fips_hvzkReal` discharges its HVZK hypothesis
with the proved simulator `hvzkSimulatorReal` under `Primitives.Laws`, for which
`Extern/MLDSA/NonVacuity.lean` holds the approved-parameter witness `mldsa_laws_inhabited`.

The numerical closure section restates the short-model CMA bound over a security-parameter-indexed
family and derives negligibility from negligible component advantages.

## Limitations

Every CMA headline (`euf_cma_security_of_nma_short`, `euf_cma_security_of_nma_fips`,
`euf_cma_security_of_nma_fips_hvzkReal`) and the per-`n` bound behind the numerical closure is
trivial at the FIPS 204 parameter sets once `qS ≥ 1`, whatever the simulator and `ζ_zk`. The
commitment step of `identificationScheme` (shared by `identificationSchemeShort`) draws the
mask `y` uniformly from all of `R_q^ℓ`, not from the `γ₁` box of FIPS 204, so `z = y + c·s₁`
is uniform and one attempt passes the response gate `‖z‖∞ < γ₁ - β` with probability exactly
`((2(γ₁ - β) - 1)/q)^(256ℓ)`: about `2^-5120`, `2^-3839` and `2^-5374` for ML-DSA-44, -65 and
-87. On a good key `hAbort` therefore forces `1 - p_abort` below that, while `hGuess` forces
`ε ≥ 1 / #w₁` with `#w₁ ≤ 44^1024`, `16^1536`, `16^2048`. The commitment-collision term
`qS·ε·(qS + 1) / (2(1 - p_abort)²)` of `FiatShamirWithAbort.cmaToNmaLoss` is then at least
`qS(qS + 1)·2^4647`, `qS(qS + 1)·2^1532` and `qS(qS + 1)·2^2555`; if no generated key is good,
`hGood` forces `δ ≥ 1` instead. This is an exact counting bound. A better HVZK simulator, and a
CMA-to-NMA step matched to it, would not change it: the root cause is the full-ring mask
sampling, a departure from FIPS 204 that has to be fixed in the scheme itself.
-/

public section

open MeasureTheory OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

open NMA

section Headline

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]
  {M : Type} [DecidableEq M]
  [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
  [SampleableType (CommitHashBytes p)]

open scoped Classical in
/-- **NMA security of ML-DSA in the idealized short-key model (Lemma 7, CRYPTO 2023).**

For every EUF-NMA adversary `A` against the ML-DSA scheme (instantiated via `FiatShamirWithAbort`
over the idealized short-secret key generation `keygenShort`), the MLWE reduction
`B = bridge A.main` and the SelfTargetMSIS reduction `C = extractorCShort p prims A.main` satisfy

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C)`.

The reductions are the concrete ones built in this file: the key-swap distinguisher
`distinguisherBShort`, whose `mldsaMLWEShort` advantage **equals** the real-vs-uniform key gap —
the short key-swap hop `nma_keyswap_hop_short` is an exact monad identity, so no statistical
slack term appears in the bound — and the SelfTargetMSIS extractor `extractorCShort`, which
turns a uniform-`t` forgery into a short self-target solution
(`nmaAdvantage_keygenShort1_le_stmsis`).

The reduction `bridge` maps each forging strategy to an adversary against the abstract MLWE
problem `mlwe`, and `hMlweBridge` states that it is at least as good, up to the slack `εbridge`, as
`distinguisherBShort` against the seed-based short problem `mldsaMLWEShort` — the
distribution the ML-DSA Module-LWE assumption is stated over (secrets uniform on the `η`-bounded
box). Under `expandAIdealization` the bridge can be instantiated against the standard
uniform-matrix problem `mldsaMatrixMLWE`, with `bridge main := matrixLift p prims
(distinguisherBShort p prims hr maxAttempts main)` and `advantage_mldsaMLWEShort_le_matrix`
(`nma_security_short_matrix`). The SelfTargetMSIS side needs no bridge: the extractor already
targets `mldsaSTMSISShort p prims M`. The hypothesis `hGen : hr.gen = keygenShort p prims` pins the
Fiat-Shamir key generation to the idealized short-key generator. The relation of `hr` is the
material-based `validKeyPairShort`, which `keygenShort` genuinely generates: the pair
`(hr, hGen)` is inhabited by `hrShort` (`keygenShort_generable`), so the statement has
non-vacuous instances.

This is the EUF-NMA half (Lemma 7) of the ML-DSA security proof in the idealized short-key model;
the CMA-to-NMA statistical step (`euf_cma_security_of_nma_short`) composes on top of it. -/
theorem nma_security_short
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGen : hr.gen = keygenShort p prims)
    (εbridge : ℝ≥0∞)
    (bridge : (PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hr maxAttempts main) ≤
        LearningWithErrors.advantage mlwe (bridge main) + εbridge) :
    ∀ (adv : SignatureAlg.EufNmaAdversary
      (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts)),
    SignatureAlg.eufNmaAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage mlwe (bridge adv.main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) := by
  classical
  intro adv
  have hB := hMlweBridge adv.main
  -- The EUF-NMA experiment is the real-`t` short-model NMA game with `main := adv.main`.
  have hadv : SignatureAlg.eufNmaAdvantage (FiatShamirWithAbort.runtime
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv =
      nmaShortAdvantage p prims hr maxAttempts (keygenShort p prims) adv.main := by
    rw [SignatureAlg.eufNmaAdvantage, nmaShortAdvantage, nmaShortExperiment]
    rw [SignatureAlg.eufNmaExperiment]
    simp only [FiatShamirWithAbort, hGen]
  rw [hadv]
  -- Bound the two NMA games by the MLWE distinguisher and the STMSIS extractor.
  set pc0 := (do
      let (pk, _) ← keygenShort p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← adv.main pk
        (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpc0
  set pc1 := (do
      let (pk, _) ← keygenShort1 p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← adv.main pk
        (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpc1
  have hg0 : nmaShortAdvantage p prims hr maxAttempts (keygenShort p prims) adv.main =
      𝒟[pc0] {true} := by
    rw [nmaShortAdvantage, nmaShortExperiment_eq_keygen_bind]
  have hg1 : nmaShortAdvantage p prims hr maxAttempts (keygenShort1 p prims) adv.main =
      𝒟[pc1] {true} := by
    rw [nmaShortAdvantage, nmaShortExperiment_eq_keygen_bind]
  -- The Boolean distance of the two games is the real-vs-uniform key gap, which the exact short
  -- key-swap hop identifies with the `mldsaMLWEShort` advantage — no statistical slack.
  have hbias : 𝒟[pc0].boolDist 𝒟[pc1] =
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
        (distinguisherBShort p prims hr maxAttempts adv.main) := by
    rw [MeasureTheory.Measure.boolDist, ← hg0, ← hg1]
    exact nma_keyswap_hop_short p prims hr maxAttempts (M := M) adv.main
  -- STMSIS extraction bound on the uniform game.
  have hstm := nmaAdvantage_keygenShort1_le_stmsis p prims hr maxAttempts (M := M) adv.main
  rw [hg1] at hstm
  -- Triangle bound: real game ≤ uniform game + MLWE advantage.
  rw [hg0]
  calc 𝒟[pc0] {true} ≤ 𝒟[pc1] {true} + 𝒟[pc0].boolDist 𝒟[pc1] :=
        MeasureTheory.Measure.apply_true_le_add_boolDist _ _
    _ ≤ SelfTargetMSIS.advantage (extractorCShort p prims adv.main) +
        (LearningWithErrors.advantage mlwe (bridge adv.main) + εbridge) := by
      rw [hbias]
      exact add_le_add hstm hB
    _ = LearningWithErrors.advantage mlwe (bridge adv.main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) := add_comm _ _

open scoped Classical in
/-- **NMA security of ML-DSA at the FIPS seed-derived key generation.**

The short-model bound `nma_security_short` transferred to the deterministic FIPS key
generator `keygen0` through the XOF-replacement assumption `expandSReplacement`: for every
EUF-NMA adversary against the ML-DSA scheme instantiated with the seed-derived key relation
(`hGen : hr.gen = keygen0 p prims`, inhabited by `hrFips` / `keygen0_generable`), the reductions
`B = bridge A.main` and `C = extractorCShort p prims A.main` satisfy

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C) + εPRG`.

The proof has exactly one new ingredient beyond the short model: the FIPS and short NMA
games share their forge-and-verify tail (`identificationScheme` and
`identificationSchemeShort` carry the same `verify` function), so the gap between the
`keygen0` game and the `keygenShort` game is one application of `hPRG` at the distinguisher
`D ρ K s₁ s₂ :=` "run the tail at the key built by `keyFromMaterial` from the material
`(ρ, K, s₁, s₂)`": its real branch is exactly the FIPS game and its ideal branch is exactly
the short game. The short-model reduction hypotheses (`hrS`/`hGenS`, `bridge`,
`hMlweBridge`) then bound the short game as in `nma_security_short`, applied to the same
forging strategy repackaged at the short scheme tag. -/
theorem nma_security_fips
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGenS : hrS.gen = keygenShort p prims)
    (εPRG : ℝ≥0∞) (hPRG : expandSReplacement p prims εPRG)
    (εbridge : ℝ≥0∞)
    (bridge : (PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hrS maxAttempts main) ≤
        LearningWithErrors.advantage mlwe (bridge main) + εbridge) :
    ∀ (adv : SignatureAlg.EufNmaAdversary
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts)),
    SignatureAlg.eufNmaAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage mlwe (bridge adv.main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) + εPRG := by
  classical
  intro adv
  have hshortBound :=
    nma_security_short p prims mlwe maxAttempts hrS hGenS εbridge bridge hMlweBridge ⟨adv.main⟩
  -- The FIPS EUF-NMA experiment is the real-`t` NMA game at `keygen0` with `main := adv.main`.
  have hadv : SignatureAlg.eufNmaAdvantage (FiatShamirWithAbort.runtime
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv =
      nmaAdvantage p prims hr maxAttempts (keygen0 p prims) adv.main := by
    rw [SignatureAlg.eufNmaAdvantage, nmaAdvantage, nmaExperiment]
    rw [SignatureAlg.eufNmaExperiment]
    simp only [FiatShamirWithAbort, hGen]
  -- The two NMA games as plain `ProbComp`s over their key generators.
  set pcF := (do
      let (pk, _) ← keygen0 p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← adv.main pk
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpcF
  set pcS := (do
      let (pk, _) ← keygenShort p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← adv.main pk
        (FiatShamirWithAbort (identificationSchemeShort p prims) hrS M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpcS
  have hgF : nmaAdvantage p prims hr maxAttempts (keygen0 p prims) adv.main =
      𝒟[pcF] {true} := by
    rw [nmaAdvantage, nmaExperiment_eq_keygen_bind]
  have hgS : SignatureAlg.eufNmaAdvantage (FiatShamirWithAbort.runtime
        (Commit := Commitment p prims) (Chal := CommitHashBytes p) M)
      (⟨adv.main⟩ : SignatureAlg.EufNmaAdversary
        (FiatShamirWithAbort (identificationSchemeShort p prims) hrS M maxAttempts)) =
      𝒟[pcS] {true} := by
    have h1 : SignatureAlg.eufNmaAdvantage (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M)
        (⟨adv.main⟩ : SignatureAlg.EufNmaAdversary
          (FiatShamirWithAbort (identificationSchemeShort p prims) hrS M maxAttempts)) =
        nmaShortAdvantage p prims hrS maxAttempts (keygenShort p prims) adv.main := by
      rw [SignatureAlg.eufNmaAdvantage, nmaShortAdvantage, nmaShortExperiment]
      rw [SignatureAlg.eufNmaExperiment]
      simp only [FiatShamirWithAbort, hGenS]
    rw [h1, nmaShortAdvantage, nmaShortExperiment_eq_keygen_bind]
  -- The PRG hop: the two games are the two branches of `hPRG` at the shared verify tail.
  have hF : 𝒟[pcF] {true} = 𝒟[do
      let seed ← $ᵗ (Bytes 32)
      let (rho, rhoPrime, _key) := prims.expandSeed seed
      let (s1, s2) := prims.expandS rhoPrime
      simulateToProbComp p prims (M := M) (do
        let d ← adv.main ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2)] {true} := by
    rw [hpcF]
    simp only [keygen0, keyFromMaterial, bind_assoc, pure_bind]
  have hS : 𝒟[pcS] {true} = 𝒟[do
      let _key ← $ᵗ (Bytes 32)
      let rho ← $ᵗ (Bytes 32)
      let s1 ← sampleShortVec p.l p.eta
      let s2 ← sampleShortVec p.k p.eta
      simulateToProbComp p prims (M := M) (do
        let d ← adv.main ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2)] {true} := by
    rw [hpcS]
    simp only [keygenShort, keyFromMaterial, bind_assoc, pure_bind]
    rfl
  have hbias : 𝒟[pcF].boolDist 𝒟[pcS] ≤ εPRG := by
    rw [MeasureTheory.Measure.boolDist, hF, hS]
    exact hPRG (fun rho _key s1 s2 => simulateToProbComp p prims (M := M) (do
      let d ← adv.main ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
        ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2))
  -- Assemble: FIPS game ≤ short game + εPRG ≤ (MLWE + εbridge) + STMSIS + εPRG.
  have hshort' : 𝒟[pcS] {true} ≤
      LearningWithErrors.advantage mlwe (bridge adv.main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) := by
    rw [← hgS]
    exact hshortBound
  rw [hadv, hgF]
  exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans (add_le_add hshort' hbias)

open scoped Classical in
/-- **EUF-CMA security of the commitment-carrying short-key ML-DSA signature.**

The CMA-to-NMA-to-hardness composition over the idealized short-secret key generation
`keygenShort`: for any EUF-CMA adversary `adv` against the Fiat-Shamir-with-aborts ML-DSA
signature, the advantage is bounded by the MLWE advantage, the SelfTargetMSIS advantage, and the
statistical CMA-to-NMA loss `FiatShamirWithAbort.cmaToNmaLoss`. The proof composes three pieces:

1. `FiatShamirWithAbort.euf_cma_to_nma`: the CMA advantage is at most the managed-RO NMA
   advantage of `simulatedNmaAdv` plus `cmaToNmaLoss`, under the
   good-key/commitment-guessing/abort/query hypotheses;
2. `FiatShamirWithAbort.managedRoNmaExperiment_simulatedNmaAdv_eq_eufNmaExperiment`:
   the managed-RO NMA experiment equals the plain EUF-NMA experiment of `simulatedEufNmaAdv`,
   the cache-forgetting reduction (steps 1 and 2 together are
   `FiatShamirWithAbort.euf_cma_to_eufNma`);
3. `nma_security_short` (Lemma 7, short model) applied to `simulatedEufNmaAdv`:
   `≤ MLWE + SelfTargetMSIS`, with no statistical key-swap slack — the short-model hop is exact.
   The reductions are `bridge` and `extractorCShort` applied to the forging strategy of
   `simulatedEufNmaAdv`.

The loss parameters carry the nonnegativity and good-key hypotheses that the abstract reduction
needs; `hGen` pins the key generation to `keygenShort`, and `bridge`/`hMlweBridge` relate the
abstract MLWE problem to the short-model one `mldsaMLWEShort`.
The relation of `hr` is the material-based `validKeyPairShort`, so `hGen` is inhabited by
`hrShort` (`keygenShort_generable`).

**Trivial at the FIPS 204 parameter sets once `qS ≥ 1`.** The commitment step draws the mask
`y` from all of `R_q^ℓ`, so on a good key `hAbort` forces
`1 - p_abort ≤ ((2(γ₁ - β) - 1)/q)^(256ℓ)`, and together with `ε ≥ 1 / #w₁` from `hGuess` the
commitment-collision term of `cmaToNmaLoss` far exceeds `1` for every `qS ≥ 1`, whatever `ζ_zk`
is; if no key is good, `hGood` forces `δ ≥ 1`. The exact figures are in the module docstring's
Limitations section.

**Open obligation: the HVZK hypothesis `hhvzk` has no witness below `ζ_zk = 1`.** In the short
model the withheld key part `t₀` is not determined by the public key across material-valid
pairs, so no single simulator is exact-on-accept for every valid pair, and the seed-model
simulator `hvzkSimulatorReal` (proved HVZK for `identificationScheme` by
`idsWithAbort_hvzk`) does not transport to `identificationSchemeShort`. The only witness
available today is `ζ_zk = 1` (any simulator, since total variation is at most one), at which
the loss `cmaToNmaLoss` contains `qS · 1 / (1 − p_abort) ≥ 1`. A quantitative short-model HVZK
bound would not by itself make the theorem non-trivial, because of the commitment-collision term
above. The seed-model composition `euf_cma_security_of_nma_fips_hvzkReal` has a proved HVZK
witness and is trivial for the same reason.

**Scope: commitment-carrying, not yet the end-to-end FIPS CMA headline.** This theorem is
stated for the standard Fiat-Shamir-with-aborts signature whose commitment is *carried* in the
signature (the generic `Option (Commitment × Response)` type). FIPS-204 ML-DSA instead
*recovers* the commitment at verification rather than carrying it; reaching that form via
commitment recovery costs one extra hash query per signing query, so the end-to-end loss grows
by `qS` to `qH + qS` — the distinction recorded in `FiatShamirWithAbort.cmaToNmaLoss`. Supplying
that commitment-recovery bridge, and composing it with the FIPS seed-derived key generation, is
follow-up work: `nma_security_fips` currently gives the seed-derived-key result at the NMA level
only. -/
theorem euf_cma_security_of_nma_short
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGen : hr.gen = keygenShort p prims)
    (sim : PublicKey p prims →
      ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk)
    (hhvzk : (identificationSchemeShort p prims).HVZK sim (ENNReal.ofReal ζ_zk))
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : PublicKey p prims → SecretKey p → Prop)
    (hGood : Pr{let xw ← hr.gen}[¬ Good xw.1 xw.2] ≤
      ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commitment p prims,
      Pr{let x ← Prod.fst <$> (identificationSchemeShort p prims).commit pk sk}[x = cm] ≤
        ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr{let x ← (identificationSchemeShort p prims).honestExecution pk sk}[x = none] ≤
        ENNReal.ofReal p_abort)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts))
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims)) (oa := adv.main pk) qS qH)
    (εbridge : ℝ≥0∞)
    (bridge : (PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hr maxAttempts main) ≤
        LearningWithErrors.advantage mlwe (bridge main) + εbridge) :
    SignatureAlg.unforgeableAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage mlwe
          (bridge (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeShort p prims) hr M
            maxAttempts sim adv).main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims
          (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeShort p prims) hr M
            maxAttempts sim adv).main) +
        ENNReal.ofReal
          (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  classical
  -- CMA advantage ≤ plain EUF-NMA advantage of `simulatedEufNmaAdv` + loss.
  have hcma := FiatShamirWithAbort.euf_cma_to_eufNma (identificationSchemeShort p prims) hr M
    maxAttempts sim adv ζ_zk hζ hhvzk qS qH ε p_abort δ hε hδ hp₀ hp Good hGood hGuess
    hAbort hQ
  -- Lemma 7, short model: the plain EUF-NMA advantage is bounded by MLWE + STMSIS.
  have hnma := nma_security_short p prims mlwe maxAttempts hr hGen εbridge bridge hMlweBridge
    (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeShort p prims) hr M
      maxAttempts sim adv)
  exact le_trans hcma (add_le_add hnma le_rfl)

open scoped Classical in
/-- **EUF-CMA security of the commitment-carrying ML-DSA signature over seed-derived keys.**

The seed-model counterpart of `euf_cma_security_of_nma_short`: the same three-step
composition (`FiatShamirWithAbort.euf_cma_to_nma`, the bridge
`FiatShamirWithAbort.managedRoNmaExperiment_simulatedNmaAdv_eq_eufNmaExperiment`, and the
NMA leg), over the FIPS-shaped key generation `keygen0` and the seed-tagged scheme
`identificationScheme`, with `nma_security_fips` as the NMA leg. Relative to the short model
the bound gains the PRG term `εPRG` of the `ExpandS` replacement hop (`expandSReplacement`); in
exchange the HVZK hypothesis is about the seed-tagged scheme, for which `idsWithAbort_hvzk`
supplies a simulator with a proved bound — see `euf_cma_security_of_nma_fips_hvzkReal`.

**Trivial at the FIPS 204 parameter sets once `qS ≥ 1`.** Even for a perfect simulator
(`ζ_zk = 0`), the full-ring mask of `identificationScheme.commit` makes the
commitment-collision term of `cmaToNmaLoss` exceed `1` at the FIPS 204 parameter sets once
`qS ≥ 1` (see the module docstring's Limitations section).

**Scope: commitment-carrying, not yet the end-to-end FIPS CMA headline.** As in the short
model, the signature carries the commitment; the commitment-recovery bridge to the FIPS-204
signature format costs `qS` extra hash queries and is follow-up work. -/
theorem euf_cma_security_of_nma_fips
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (hGenS : hrS.gen = keygenShort p prims)
    (εPRG : ℝ≥0∞) (hPRG : expandSReplacement p prims εPRG)
    (sim : PublicKey p prims →
      ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk)
    (hhvzk : (identificationScheme p prims).HVZK sim (ENNReal.ofReal ζ_zk))
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : PublicKey p prims → SecretKey p → Prop)
    (hGood : Pr{let xw ← hr.gen}[¬ Good xw.1 xw.2] ≤
      ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commitment p prims,
      Pr{let x ← Prod.fst <$> (identificationScheme p prims).commit pk sk}[x = cm] ≤
        ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr{let x ← (identificationScheme p prims).honestExecution pk sk}[x = none] ≤
        ENNReal.ofReal p_abort)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts))
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims)) (oa := adv.main pk) qS qH)
    (εbridge : ℝ≥0∞)
    (bridge : (PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hrS maxAttempts main) ≤
        LearningWithErrors.advantage mlwe (bridge main) + εbridge) :
    SignatureAlg.unforgeableAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage mlwe
          (bridge (FiatShamirWithAbort.simulatedEufNmaAdv (identificationScheme p prims) hr M
            maxAttempts sim adv).main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims
          (FiatShamirWithAbort.simulatedEufNmaAdv (identificationScheme p prims) hr M
            maxAttempts sim adv).main) +
        εPRG +
        ENNReal.ofReal
          (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  classical
  -- CMA advantage ≤ plain EUF-NMA advantage of `simulatedEufNmaAdv` + loss.
  have hcma := FiatShamirWithAbort.euf_cma_to_eufNma (identificationScheme p prims) hr M
    maxAttempts sim adv ζ_zk hζ hhvzk qS qH ε p_abort δ hε hδ hp₀ hp Good hGood hGuess
    hAbort hQ
  -- Seed model: the plain EUF-NMA advantage is bounded by MLWE + STMSIS + PRG.
  have hnma := nma_security_fips p prims mlwe maxAttempts hr hGen hrS hGenS εPRG hPRG εbridge
    bridge hMlweBridge
    (FiatShamirWithAbort.simulatedEufNmaAdv (identificationScheme p prims) hr M
      maxAttempts sim adv)
  exact le_trans hcma (add_le_add hnma le_rfl)

open scoped Classical in
/-- `euf_cma_security_of_nma_fips` with the HVZK hypothesis discharged by the proved
seed-model simulator: under the primitive laws `h_laws`, `idsWithAbort_hvzk` gives
`hvzkSimulatorReal` at the bound `hvzkBound`, so the HVZK term of the loss is the proved
quantity `(hvzkBound p prims).toReal` (the bound is a supremum of probabilities, hence finite)
rather than a hypothesis.

**Trivial for any adversary that signs, at the FIPS 204 parameters.** The commitment step of
`identificationScheme` draws the mask `y` from all of `R_q^ℓ`, so `z = y + c·s₁` is uniform and
one attempt passes the response gate with probability exactly `((2(γ₁ − β) − 1)/q)^(256ℓ)`. On a
good key `hAbort` then forces `1 − p_abort` below that, and `hGuess` forces `ε ≥ 1 / #w₁`, so the
commitment-collision term `qS·ε·(qS + 1) / (2(1 − p_abort)²)` of `cmaToNmaLoss` is at least
`qS(qS + 1)·2^1532` at every FIPS 204 parameter set; if no generated key is good, `hGood` forces
`δ ≥ 1` instead. This is an exact counting bound (figures in the module docstring's Limitations
section), and it holds whatever the simulator is: no HVZK simulator or CMA-to-NMA step matched
to it would make this statement non-trivial while the mask ranges over the whole ring. The
statement is non-trivial only at `qS = 0`.

The HVZK term is separately large. `hvzkBound` is the supremum over seeds of `hvzkBadMass`,
the probability that the response gate passes while a secret-dependent gate (`LowBits`, `c·t₀`,
hint weight) fails, and the loss divides it by `1 − p_abort`. -/
theorem euf_cma_security_of_nma_fips_hvzkReal
    (h_laws : Primitives.Laws prims nttOps)
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (hGenS : hrS.gen = keygenShort p prims)
    (εPRG : ℝ≥0∞) (hPRG : expandSReplacement p prims εPRG)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : PublicKey p prims → SecretKey p → Prop)
    (hGood : Pr{let xw ← hr.gen}[¬ Good xw.1 xw.2] ≤
      ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commitment p prims,
      Pr{let x ← Prod.fst <$> (identificationScheme p prims).commit pk sk}[x = cm] ≤
        ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr{let x ← (identificationScheme p prims).honestExecution pk sk}[x = none] ≤
        ENNReal.ofReal p_abort)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts))
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims)) (oa := adv.main pk) qS qH)
    (εbridge : ℝ≥0∞)
    (bridge : (PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hrS maxAttempts main) ≤
        LearningWithErrors.advantage mlwe (bridge main) + εbridge) :
    SignatureAlg.unforgeableAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage mlwe
          (bridge (FiatShamirWithAbort.simulatedEufNmaAdv (identificationScheme p prims) hr M
            maxAttempts (hvzkSimulatorReal p prims) adv).main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims
          (FiatShamirWithAbort.simulatedEufNmaAdv (identificationScheme p prims) hr M
            maxAttempts (hvzkSimulatorReal p prims) adv).main) +
        εPRG +
        ENNReal.ofReal (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort
          (hvzkBound p prims).toReal δ hp) := by
  have hne : hvzkBound p prims ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (iSup_le fun _ => hvzkBadMass_le_one p prims _ _)
  exact euf_cma_security_of_nma_fips p prims mlwe maxAttempts hr hGen hrS hGenS
    εPRG hPRG (hvzkSimulatorReal p prims) (hvzkBound p prims).toReal ENNReal.toReal_nonneg
    (by rw [ENNReal.ofReal_toReal hne]; exact idsWithAbort_hvzk p prims h_laws)
    qS qH ε p_abort δ hε hδ hp₀ hp Good hGood hGuess
    hAbort adv hQ εbridge bridge hMlweBridge

/-! ## Numerical EUF-CMA closure under uniform advantage bounds

The security-parameter-indexed closure of the loss regime. The scheme is indexed by `n`
through a *family* `(p n, prims n)` of ML-DSA parameter/primitive instances, so that the
commitment guessing probability `ε n`, the key-regularity failure `δ n`, the HVZK slack
`ζ_zk n`, and the MLWE-bridge slack `εbridge n` all shrink (negligibly) as `n → ∞` while the
signing / hashing query budgets `qS n`, `qH n` grow only polynomially in `n`. Under negligible
MLWE and SelfTargetMSIS advantage families this makes the EUF-CMA advantage family negligible.
The advantage-bound families are required to dominate *every* reduction adversary, with no
cost model restricting them, so this is a numerical closure rather than a computational
(asymptotic) security theorem.

A fixed-scheme wrapper would be degenerate: with a *constant* `ε > 0` the loss term
`2·qS·(qH+1)·ε/(1−p)` is only negligible when the query budgets vanish. Here the slacks are
themselves negligible families, so each loss term is `poly(n) · negligible(n)`, which is negligible
by `negligible_polynomial_mul`. -/

omit nttOps in
/-- A geometric family `r ^ n` with `0 ≤ r < 1` is negligible (after `ENNReal.ofReal`): for every
power `k`, `n ^ k · r ^ n → 0` (`tendsto_pow_const_mul_const_pow_of_lt_one`), and `ENNReal.ofReal`
is continuous. This provides concrete negligible slack/advantage families for the non-vacuity
witness `asymptotic_loss_regime_satisfiable`. -/
theorem negligible_ofReal_geometric (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    negligible (fun n => ENNReal.ofReal (r ^ n)) := by
  intro k
  have hreal : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ k * r ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one k hr0 hr1
  have h2 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ k * r ^ n)) Filter.atTop
      (nhds (ENNReal.ofReal 0)) :=
    (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  rw [ENNReal.ofReal_zero] at h2
  refine h2.congr (fun n => ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast]

omit nttOps in
/-- Building block: a fixed-constant multiple of `qS ^ dS · qH ^ dH · slack n` is negligible
whenever `qS`, `qH` are polynomially bounded and `slack` is a negligible (real-valued) family. The
product is bounded above by `(poly evaluation) · (constant) · ofReal (slack n)`; the polynomial
absorbs the query powers and the negligible slack drives the product to `0` faster than any
polynomial via `negligible_polynomial_mul`. -/
private theorem negl_poly_slack
    (qS qH : ℕ → ℕ) (slack : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (pS pH : Polynomial ℕ) (dS dH : ℕ)
    (hqS : ∀ n, qS n ≤ pS.eval n) (hqH : ∀ n, qH n ≤ pH.eval n)
    (hslackneg : negligible (fun n => ENNReal.ofReal (slack n))) :
    negligible (fun n => ENNReal.ofReal (c * (qS n) ^ dS * (qH n) ^ dH * slack n)) := by
  have hbound : ∀ n, ENNReal.ofReal (c * (qS n) ^ dS * (qH n) ^ dH * slack n) ≤
      (↑((pS.eval n) ^ dS * (pH.eval n) ^ dH) : ℝ≥0∞) *
        (ENNReal.ofReal c * ENNReal.ofReal (slack n)) := by
    intro n
    rcases le_or_gt 0 (slack n) with hs | hs
    · rw [show c * (qS n : ℝ) ^ dS * (qH n : ℝ) ^ dH * slack n
            = ((qS n : ℝ) ^ dS * (qH n : ℝ) ^ dH) * (c * slack n) by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc]
      gcongr
      rw [show ((qS n : ℝ) ^ dS * (qH n : ℝ) ^ dH)
            = ((((qS n) ^ dS) * ((qH n) ^ dH) : ℕ) : ℝ) by push_cast; ring,
          ENNReal.ofReal_natCast]
      exact_mod_cast Nat.mul_le_mul (Nat.pow_le_pow_left (hqS n) dS)
        (Nat.pow_le_pow_left (hqH n) dH)
    · have hle : c * (qS n : ℝ) ^ dS * (qH n : ℝ) ^ dH * slack n ≤ 0 := by
        have hpos : (0 : ℝ) ≤ c * (qS n : ℝ) ^ dS * (qH n : ℝ) ^ dH := by positivity
        nlinarith
      rw [ENNReal.ofReal_of_nonpos hle]; exact zero_le
  refine negligible_of_le hbound ?_
  have hconst : negligible (fun n => ENNReal.ofReal c * ENNReal.ofReal (slack n)) :=
    negligible_const_mul hslackneg ENNReal.ofReal_ne_top
  have hpoly := negligible_polynomial_mul hconst (pS ^ dS * pH ^ dH)
  refine negligible_of_le (fun n => ?_) hpoly
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]

omit nttOps in
/-- **The CMA-to-NMA statistical loss is a negligible family** when the abort rate `p_abort` is a
fixed constant `< 1`, the signing / hashing budgets `qS`, `qH` are polynomially bounded, and the
three per-key slacks `ε` (commitment guessing), `ζ_zk` (HVZK), and `δ` (key regularity) are
negligible families. Each of the four loss terms is a fixed-constant multiple of a polynomial in the
query budgets times a negligible slack, hence negligible by `negl_poly_slack`; the final `δ` term is
negligible by hypothesis. The total `cmaToNmaLoss` is bounded by their sum (subadditivity of
`ENNReal.ofReal`). -/
theorem cmaToNmaLoss_negligible
    (qS qH : ℕ → ℕ) (ε ζ_zk δ : ℕ → ℝ) (p_abort : ℝ) (hp : p_abort < 1)
    (pS pH : Polynomial ℕ)
    (hqS : ∀ n, qS n ≤ pS.eval n) (hqH : ∀ n, qH n ≤ pH.eval n)
    (hεneg : negligible (fun n => ENNReal.ofReal (ε n)))
    (hζneg : negligible (fun n => ENNReal.ofReal (ζ_zk n)))
    (hδneg : negligible (fun n => ENNReal.ofReal (δ n))) :
    negligible (fun n => ENNReal.ofReal
      (FiatShamirWithAbort.cmaToNmaLoss (qS n) (qH n) (ε n) p_abort (ζ_zk n) (δ n) hp)) := by
  have h1mp : (0 : ℝ) < 1 - p_abort := by linarith
  have t1 := negl_poly_slack qS (fun n => qH n + 1) ε (2 / (1 - p_abort))
    (by positivity) pS (pH + 1) 1 1 hqS
    (fun n => by simpa [Polynomial.eval_add] using Nat.add_le_add_right (hqH n) 1) hεneg
  have t2 := negl_poly_slack (fun n => qS n * (qS n + 1)) qH ε (1 / (2 * (1 - p_abort) ^ 2))
    (by positivity) (pS * (pS + 1)) pH 1 0
    (fun n => by
      rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
      exact Nat.mul_le_mul (hqS n) (Nat.add_le_add_right (hqS n) 1))
    (fun n => hqH n) hεneg
  have t3 := negl_poly_slack qS qH ζ_zk (1 / (1 - p_abort)) (by positivity) pS pH 1 0
    hqS hqH hζneg
  have hsum := negligible_add (negligible_add (negligible_add t1 t2) t3) hδneg
  refine negligible_of_le (g := fun n =>
      ENNReal.ofReal (2 / (1 - p_abort) * (qS n : ℝ) ^ 1 * ((qH n + 1 : ℕ) : ℝ) ^ 1 * ε n) +
      ENNReal.ofReal (1 / (2 * (1 - p_abort) ^ 2) * ((qS n * (qS n + 1) : ℕ) : ℝ) ^ 1 *
        (qH n : ℝ) ^ 0 * ε n) +
      ENNReal.ofReal (1 / (1 - p_abort) * (qS n : ℝ) ^ 1 * (qH n : ℝ) ^ 0 * ζ_zk n) +
      ENNReal.ofReal (δ n)) (fun n => ?_) hsum
  have heq : (FiatShamirWithAbort.cmaToNmaLoss (qS n) (qH n) (ε n) p_abort (ζ_zk n) (δ n) hp)
      = (2 / (1 - p_abort) * (qS n : ℝ) ^ 1 * ((qH n + 1 : ℕ) : ℝ) ^ 1 * ε n) +
        (1 / (2 * (1 - p_abort) ^ 2) * ((qS n * (qS n + 1) : ℕ) : ℝ) ^ 1 *
          (qH n : ℝ) ^ 0 * ε n) +
        (1 / (1 - p_abort) * (qS n : ℝ) ^ 1 * (qH n : ℝ) ^ 0 * ζ_zk n) + δ n := by
    rw [FiatShamirWithAbort.cmaToNmaLoss]; push_cast; field_simp
  rw [heq]
  calc ENNReal.ofReal (_ + _ + _ + δ n)
      ≤ ENNReal.ofReal (_ + _ + _) + ENNReal.ofReal (δ n) := ENNReal.ofReal_add_le
    _ ≤ _ + ENNReal.ofReal _ + ENNReal.ofReal (δ n) := by gcongr; exact ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal _ + ENNReal.ofReal _ + ENNReal.ofReal _ + ENNReal.ofReal (δ n) := by
        gcongr; exact ENNReal.ofReal_add_le

omit nttOps in
/-- **Numerical EUF-CMA closure of ML-DSA in the idealized short-key model under uniform
advantage bounds.**

This is a numerical statement, not computational security: `hMlweBound` and `hStmsisBound`
dominate every adversary, unrestricted by any cost model, so the theorem records that the loss
regime closes under such bounds rather than establishing asymptotic security. The ML-DSA
scheme is given as a
*family* `(p n, prims n)` over the security parameter `n`, with all carrier instances
supplied per `n`. The hypotheses are the `n`-indexed lifts of those of
`euf_cma_security_of_nma_short`, plus:

* polynomial query bounds `qS n ≤ pS.eval n`, `qH n ≤ pH.eval n`;
* negligible commitment-guessing slack `ε`, key-regularity slack `δ`, HVZK slack `ζ_zk`,
  and MLWE-bridge slack `εbridge` families (the commitment / response spaces grow with `n`);
* negligible families `mlweAdv`, `stmsisAdv` bounding the MLWE and SelfTargetMSIS advantages
  of every adversary, with no cost bound on the adversary.

The conclusion is that the EUF-CMA advantage family of `adv` is negligible. The proof
instantiates the per-`n` bound `euf_cma_security_of_nma_short`, bounds the MLWE reduction chosen
from `hMlweBridge` and the SelfTargetMSIS extractor by their negligible families, and bounds
the statistical loss family with `cmaToNmaLoss_negligible`: with polynomially-bounded queries
and negligible slacks each loss term is `poly(n) · negligible(n)`.

No cost model is attached: the statement quantifies over unrestricted adversaries and
`n`-indexed advantage families, not over poly-time adversaries.

**The hypotheses are jointly unsatisfiable for ML-DSA-shaped families; this theorem is a
formal closure of the loss algebra only.**

* `hAbort` at a constant `p_abort < 1`, `hGood` and `hδneg` cannot hold together once the
  response-gate acceptance `((2(γ₁ - β) - 1)/q)^(256ℓ)` of the full-ring mask drops below
  `1 - p_abort`, which it does for every ML-DSA-shaped family: `hAbort` then fails on every key,
  so `Good n` is empty on the support of `(hr n).gen`, `hGood` forces `δ n ≥ 1`, and `hδneg` fails.
* `hMlweBound` and `hStmsisBound` bound unbounded adversaries. For any family in which
  `mldsaSTMSISShort` has solutions, an unbounded extractor finds one with probability close to
  `1`, so `hStmsisBound` with a negligible `stmsisAdv` fails; exhaustive search likewise gives
  MLWE advantage close to `1` on non-degenerate instances, so `hMlweBound` with a negligible
  `mlweAdv` fails.
* `hhvzk` together with `hζneg` needs a short-model HVZK simulator family with negligible error,
  and none is known below `ζ_zk = 1` (see `euf_cma_security_of_nma_short`).

`asymptotic_loss_regime_satisfiable` shows only that the numerical side conditions can be met
with growing query budgets; it instantiates none of these hypotheses. -/
theorem euf_cma_security_short_of_uniform_advantage_bounds
    (p' : ℕ → Params) (prims' : ∀ n, Primitives (p' n)) [nttOps' : NTTRingOps]
    (instHigh : ∀ n, DecidableEq (prims' n).High)
    {M' : Type} [DecidableEq M']
    (instCommInh : ∀ n, Inhabited (Commitment (p' n) (prims' n)))
    (instRespInh : ∀ n, Inhabited (Response (p' n) (prims' n)))
    (instChal : ∀ n, SampleableType (CommitHashBytes (p' n)))
    (mlwe : ∀ n, LearningWithErrors.Problem (TqMatrix (p' n).k (p' n).l)
      (RqVec (p' n).l) (RqVec (p' n).k))
    (maxAttempts : ℕ → ℕ)
    (hr : ∀ n, GenerableRelation (PublicKey (p' n) (prims' n)) (SecretKey (p' n))
      (validKeyPairShort (p' n) (prims' n)))
    (hGen : ∀ n, (hr n).gen = keygenShort (p' n) (prims' n))
    (sim : ∀ n, PublicKey (p' n) (prims' n) → ProbComp
      (Option (Commitment (p' n) (prims' n) × CommitHashBytes (p' n) ×
        Response (p' n) (prims' n))))
    (ζ_zk : ℕ → ℝ) (hζ : ∀ n, 0 ≤ ζ_zk n)
    (hhvzk : ∀ n, (identificationSchemeShort (p' n) (prims' n)).HVZK (sim n)
      (ENNReal.ofReal (ζ_zk n)))
    (qS qH : ℕ → ℕ) (ε δ : ℕ → ℝ) (p_abort : ℝ)
    (hp : p_abort < 1) (hp₀ : 0 ≤ p_abort)
    (hε : ∀ n, 0 ≤ ε n) (hδ : ∀ n, 0 ≤ δ n)
    (Good : ∀ n, PublicKey (p' n) (prims' n) → SecretKey (p' n) → Prop)
    (hGood : ∀ n, Pr{let xw ← (hr n).gen}[¬ Good n xw.1 xw.2] ≤ ENNReal.ofReal (δ n))
    (hGuess : ∀ n, ∀ pk sk, Good n pk sk → ∀ cm : Commitment (p' n) (prims' n),
      Pr{let x ← Prod.fst <$> (identificationSchemeShort (p' n) (prims' n)).commit pk sk}[x = cm] ≤
        ENNReal.ofReal (ε n))
    (hAbort : ∀ n, ∀ pk sk, Good n pk sk →
      Pr{let x ← (identificationSchemeShort (p' n) (prims' n)).honestExecution pk sk}[x = none] ≤
        ENNReal.ofReal p_abort)
    (adv : ∀ n, SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort (identificationSchemeShort (p' n) (prims' n)) (hr n) M'
        (maxAttempts n)))
    (hQ : ∀ n, ∀ pk, FiatShamir.signHashQueryBound M'
      (S' := Option (Commitment (p' n) (prims' n) × Response (p' n) (prims' n)))
      (oa := (adv n).main pk) (qS n) (qH n))
    (εbridge : ℕ → ℝ≥0∞)
    (hMlweBridge : ∀ n, ∀ (main : PublicKey (p' n) (prims' n) →
        OracleComp (unifSpec + (M' × Commitment (p' n) (prims' n) →ₒ CommitHashBytes (p' n)))
          (M' × Option (Commitment (p' n) (prims' n) × Response (p' n) (prims' n)))),
      ∃ B : LearningWithErrors.Adversary (mlwe n),
        LearningWithErrors.advantage (mldsaMLWEShort (p' n) (prims' n))
          (distinguisherBShort (p' n) (prims' n) (hr n) (maxAttempts n) main) ≤
          LearningWithErrors.advantage (mlwe n) B + εbridge n)
    (pS pH : Polynomial ℕ)
    (hqS : ∀ n, qS n ≤ pS.eval n) (hqH : ∀ n, qH n ≤ pH.eval n)
    (mlweAdv stmsisAdv : ℕ → ℝ≥0∞)
    (hmlweNegl : negligible mlweAdv) (hstmsisNegl : negligible stmsisAdv)
    (hMlweBound : ∀ n (B : LearningWithErrors.Adversary (mlwe n)),
      LearningWithErrors.advantage (mlwe n) B ≤ mlweAdv n)
    (hStmsisBound : ∀ n (C : SelfTargetMSIS.Adversary (mldsaSTMSISShort (p' n) (prims' n) M')),
      SelfTargetMSIS.advantage C ≤ stmsisAdv n)
    (hbridgeNegl : negligible εbridge)
    (hεneg : negligible (fun n => ENNReal.ofReal (ε n)))
    (hδneg : negligible (fun n => ENNReal.ofReal (δ n)))
    (hζneg : negligible (fun n => ENNReal.ofReal (ζ_zk n))) :
    negligible (fun n => SignatureAlg.unforgeableAdvantage
      (FiatShamirWithAbort.runtime
        (Commit := Commitment (p' n) (prims' n)) (Chal := CommitHashBytes (p' n)) M') (adv n)) := by
  have hbound : ∀ n, SignatureAlg.unforgeableAdvantage
      (FiatShamirWithAbort.runtime
        (Commit := Commitment (p' n) (prims' n)) (Chal := CommitHashBytes (p' n)) M') (adv n) ≤
      mlweAdv n + εbridge n + stmsisAdv n +
      ENNReal.ofReal (FiatShamirWithAbort.cmaToNmaLoss (qS n) (qH n) (ε n) p_abort
        (ζ_zk n) (δ n) hp) := by
    intro n
    have hb :=
      @euf_cma_security_of_nma_short (p' n) (prims' n) nttOps' (instHigh n) M' _
        (instCommInh n) (instRespInh n)
        (instChal n)
        (mlwe n) (maxAttempts n) (hr n) (hGen n)
        (sim n) (ζ_zk n) (hζ n) (hhvzk n)
        (qS n) (qH n) (ε n) p_abort (δ n) (hε n) (hδ n) hp₀ hp (Good n) (hGood n) (hGuess n)
        (hAbort n) (adv n) (hQ n) (εbridge n)
        (fun main => (hMlweBridge n main).choose) (fun main => (hMlweBridge n main).choose_spec)
    exact le_trans hb (add_le_add (add_le_add (add_le_add (hMlweBound n _) le_rfl)
      (hStmsisBound n _)) le_rfl)
  refine negligible_of_le hbound ?_
  refine negligible_add (negligible_add (negligible_add hmlweNegl hbridgeNegl) hstmsisNegl) ?_
  exact cmaToNmaLoss_negligible qS qH ε ζ_zk δ p_abort hp pS pH hqS hqH hεneg hζneg hδneg

omit nttOps in
/-- **Consistency of the asymptotic numerical-loss regime.**

The numerical side conditions of `euf_cma_security_short_of_uniform_advantage_bounds` — the
query-budget and slack sequences: *polynomially-bounded* query budgets together with
*negligible* statistical slacks (commitment guessing `ε`, HVZK `ζ_zk`, key regularity `δ`, MLWE
bridge `εbridge`) and negligible advantage sequences — can be met with query budgets that
genuinely **grow** with the security parameter. Concretely, taking `qS n = qH n = n` (bounded
by `Polynomial.X`, i.e. *not* vanishing), all slacks and advantage families equal to
`(1 / 2) ^ n`, and `p_abort = 1 / 2`, the resulting `cmaToNmaLoss` family, together with the two
advantage sequences and the bridge slack, is negligible — so the dominating sum in the headline's
internal bound is negligible.

This rules out the degenerate reading of the headline (where polynomial queries against a
*fixed* positive `ε` would force the budgets to vanish): here the budgets grow polynomially
while the loss still decays.

This statement chooses **numerical sequences only**. It does not instantiate the hardness
problems, `hMlweBridge`, the HVZK simulator family, the scheme family, or the other
hypotheses of `euf_cma_security_short_of_uniform_advantage_bounds`; it describes the loss
regime, not the satisfiability of the security theorem. -/
theorem asymptotic_loss_regime_satisfiable :
    ∃ (qS qH : ℕ → ℕ) (ε ζ_zk δ : ℕ → ℝ) (εbridge : ℕ → ℝ≥0∞) (p_abort : ℝ) (hp : p_abort < 1)
      (pS pH : Polynomial ℕ) (mlweAdv stmsisAdv : ℕ → ℝ≥0∞),
      (∀ n, qS n ≤ pS.eval n) ∧ (∀ n, qH n ≤ pH.eval n) ∧
      -- the queries genuinely grow (are not the degenerate vanishing-query regime)
      (∀ n, qS n = n) ∧ (∀ n, qH n = n) ∧
      negligible mlweAdv ∧ negligible stmsisAdv ∧
      negligible (fun n => ENNReal.ofReal (ε n)) ∧
      negligible (fun n => ENNReal.ofReal (ζ_zk n)) ∧
      negligible (fun n => ENNReal.ofReal (δ n)) ∧
      negligible εbridge ∧
      negligible (fun n => mlweAdv n + εbridge n + stmsisAdv n +
        ENNReal.ofReal (FiatShamirWithAbort.cmaToNmaLoss (qS n) (qH n) (ε n) p_abort
          (ζ_zk n) (δ n) hp)) := by
  have hgrow : ∀ n : ℕ, n ≤ (Polynomial.X : Polynomial ℕ).eval n := fun n => by simp
  have hneg : negligible (fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) :=
    negligible_ofReal_geometric (1 / 2) (by norm_num) (by norm_num)
  have hEeq : ∀ n : ℕ, (1 / 2 : ℝ≥0∞) ^ n = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n
    rw [ENNReal.ofReal_pow (by norm_num)]
    congr 1
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp [ENNReal.ofReal_one]
  have hnegE : negligible (fun n => (1 / 2 : ℝ≥0∞) ^ n) := by
    simp only [hEeq]; exact hneg
  refine ⟨fun n => n, fun n => n, fun n => (1 / 2) ^ n, fun n => (1 / 2) ^ n,
    fun n => (1 / 2) ^ n, fun n => (1 / 2) ^ n, 1 / 2, by norm_num, Polynomial.X, Polynomial.X,
    fun n => (1 / 2) ^ n, fun n => (1 / 2) ^ n, hgrow, hgrow, fun _ => rfl, fun _ => rfl,
    hnegE, hnegE, hneg, hneg, hneg, hnegE, ?_⟩
  refine negligible_add (negligible_add (negligible_add hnegE hnegE) hnegE) ?_
  exact cmaToNmaLoss_negligible (fun n => n) (fun n => n) (fun n => (1 / 2) ^ n)
    (fun n => (1 / 2) ^ n) (fun n => (1 / 2) ^ n) (1 / 2) (by norm_num) Polynomial.X Polynomial.X
    hgrow hgrow hneg hneg hneg

end Headline

section MatrixHeadline

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]
  {M : Type} [DecidableEq M]
  [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
  [SampleableType (CommitHashBytes p)]

/-- **The matrix-MLWE-facing NMA headline.** `nma_security_short` with the abstract-problem
bridge discharged: the MLWE leg lands on the standard uniform-matrix short-secret problem
`mldsaMatrixMLWE`, at the cost of one application of the `expandAIdealization` assumption
(`advantage_mldsaMLWEShort_le_matrix`, supplying the bridge slack `εA`).

**Non-quantitative.** `expandAIdealization` has no instance below `εA ≈ 1` (see its docstring),
so this corollary carries no security content at any parameter set; it records the shape of the
seed-to-matrix bridge. The quantitative statement over the uniform-matrix problem is
`MLDSA.NMA.nma_security_rom` in `LatticeCrypto.MLDSA.SecurityExpandARO`, which models `ExpandA`
as a random oracle shared by key generation, verification, and the reduction instead of assuming
a property of the fixed `prims.expandA`.

The SelfTargetMSIS leg lands on the *tailored* `mldsaSTMSISShort`, not the standard
SelfTargetMSIS normal form — that second bridge is follow-up work, so only the MLWE side is
stated against a standard literature problem here. -/
theorem nma_security_short_matrix (maxAttempts : ℕ) (εA : ℝ≥0∞)
    (hA : NMA.expandAIdealization p prims εA)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (hGen : hr.gen = NMA.keygenShort p prims) :
    ∀ (adv : SignatureAlg.EufNmaAdversary
      (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts)),
    SignatureAlg.eufNmaAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage (NMA.mldsaMatrixMLWE p)
          (NMA.matrixLift p prims (NMA.distinguisherBShort p prims hr maxAttempts adv.main)) +
        εA +
        SelfTargetMSIS.advantage (NMA.extractorCShort p prims adv.main) :=
  nma_security_short p prims (NMA.mldsaMatrixMLWE p) maxAttempts hr hGen εA
    (fun main => NMA.matrixLift p prims (NMA.distinguisherBShort p prims hr maxAttempts main))
    (fun _ => NMA.advantage_mldsaMLWEShort_le_matrix p prims hA _)

end MatrixHeadline

end MLDSA
