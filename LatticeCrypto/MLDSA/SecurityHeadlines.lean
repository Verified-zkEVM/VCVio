/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.MLDSA.SecurityNMA

/-!
# ML-DSA EUF-NMA headlines

The composed EUF-NMA statements over the reductions of `LatticeCrypto.MLDSA.SecurityNMA`
(Lemma 7 of Barbosa et al., CRYPTO 2023). Each bounds the EUF-NMA advantage of a named forger by
the advantages of named reductions:

* `nma_security_short`: the idealized short-key scheme, against an abstract MLWE problem over
  any sample type through a supplied reduction `bridge` and slack `εbridge`;
* `nma_security_short_seed`: the same at the seed-based short problem `mldsaMLWEShort`, with no
  supplied bridge and zero slack;
* `nma_security_fips`: the FIPS seed-derived key generation `keygen0`, which adds the
  `expandSAdvantage` of the named distinguisher `expandSDistinguisher`;
* `nma_security_fips_seed`: `nma_security_fips` at `mldsaMLWEShort` with zero bridge slack.

The uniform-matrix form, with `ExpandA` a programmed random oracle, is
`MLDSA.NMA.nma_security_rom` in `LatticeCrypto.MLDSA.SecurityExpandARO`.

## Limitations

* The SelfTargetMSIS leg lands on the *tailored* problem `mldsaSTMSISShort`, the ML-DSA verifier
  relation, not the standard SelfTargetMSIS normal form (see *Tailored vs. standard
  SelfTargetMSIS* in `LatticeCrypto.MLDSA.SecurityNMA`).
* `mldsaMLWEShort` presents the matrix through a seed for the fixed function `prims.expandA`.
* No cost model is attached to any reduction (#460). In particular `expandSAdvantage` is charged
  for one named distinguisher; reading it as small is a PRG assumption on the SHAKE-based
  `ExpandSeed`/`ExpandS` against that distinguisher's cost, and it is close to `1` over all
  distinguishers.
* The EUF-CMA composition is not stated here. The NMA game has no signing oracle, so these bounds
  do not depend on the commitment step of `identificationScheme`. The CMA-to-NMA loss does: that
  step samples the mask from all of `R_q^ℓ` rather than from the `γ₁` box of FIPS 204, which makes
  the commitment-collision term of `FiatShamirWithAbort.cmaToNmaLoss` exceed `1` at the FIPS 204
  parameter sets once `qS ≥ 1` (#995).
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
box). At `mlwe := mldsaMLWEShort` the bridge is the identity at zero slack
(`nma_security_short_seed`); the uniform-matrix problem `mldsaMatrixMLWE` is reached by modelling
`ExpandA` as a random oracle instead (`MLDSA.NMA.nma_security_rom`). The SelfTargetMSIS side
needs no bridge: the extractor already
targets `mldsaSTMSISShort p prims M`. The hypothesis `hGen : hr.gen = keygenShort p prims` pins the
Fiat-Shamir key generation to the idealized short-key generator. The relation of `hr` is the
material-based `validKeyPairShort`, which `keygenShort` genuinely generates: the pair
`(hr, hGen)` is inhabited by `hrShort` (`keygenShort_generable`), so the statement has
non-vacuous instances.

This is the EUF-NMA half (Lemma 7) of the ML-DSA security proof in the idealized short-key model.
The CMA-to-NMA step is not composed here. -/
theorem nma_security_short {Sample : Type}
    (mlwe : LearningWithErrors.Problem Sample (RqVec p.l) (RqVec p.k))
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
/-- **NMA security of ML-DSA in the idealized short-key model, against seed-based MLWE.**

`nma_security_short` with no supplied bridge: the MLWE reduction is the key-swap distinguisher
`distinguisherBShort` itself, played against the seed-based short problem `mldsaMLWEShort`, at
zero bridge slack. For every EUF-NMA adversary `A`,

  `Adv^{EUF-NMA}(A) ≤ Adv^{MLWE-seed}(distinguisherBShort A) + Adv^{SelfTargetMSIS}(C)`.

The MLWE problem here draws the matrix as `ExpandA(ρ)` from a uniform public seed `ρ`; the
uniform-matrix form without idealization slack is `MLDSA.NMA.nma_security_rom` in
`LatticeCrypto.MLDSA.SecurityExpandARO`, which models `ExpandA` as a programmed random oracle. -/
theorem nma_security_short_seed
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGen : hr.gen = keygenShort p prims) :
    ∀ (adv : SignatureAlg.EufNmaAdversary
      (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts)),
    SignatureAlg.eufNmaAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hr maxAttempts adv.main) +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) := by
  intro adv
  simpa only [add_zero] using
    nma_security_short p prims (mldsaMLWEShort p prims) maxAttempts hr hGen 0
      (distinguisherBShort p prims hr maxAttempts) (fun _ => le_of_eq (add_zero _).symm) adv

open scoped Classical in
/-- **NMA security of ML-DSA at the FIPS seed-derived key generation.**

The short-model bound `nma_security_short` transferred to the deterministic FIPS key
generator `keygen0`: for every EUF-NMA adversary against the ML-DSA scheme instantiated with the
seed-derived key relation (`hGen : hr.gen = keygen0 p prims`, inhabited by `hrFips` /
`keygen0_generable`), the reductions `B = bridge A.main`, `C = extractorCShort p prims A.main`
and `D = expandSDistinguisher p prims hr maxAttempts A.main` satisfy

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C) + Adv^{ExpandS}(D)`.

The proof has exactly one new ingredient beyond the short model: the FIPS and short NMA
games share their forge-and-verify tail (`identificationScheme` and
`identificationSchemeShort` carry the same `verify` function), so the gap between the
`keygen0` game and the `keygenShort` game is the `expandSAdvantage` of `D`, which runs that tail
at the public key built from the material `(ρ, K, s₁, s₂)`: its real branch is exactly the FIPS
game and its ideal branch is exactly the short game. The short-model reduction hypotheses
(`hrS`/`hGenS`, `bridge`, `hMlweBridge`) then bound the short game as in `nma_security_short`,
applied to the same forging strategy repackaged at the short scheme tag. -/
theorem nma_security_fips {Sample : Type}
    (mlwe : LearningWithErrors.Problem Sample (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGenS : hrS.gen = keygenShort p prims)
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
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) +
        expandSAdvantage p prims (expandSDistinguisher p prims hr maxAttempts adv.main) := by
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
  -- The `ExpandS` hop: the two games are the two branches of the replacement game at `D`.
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
  have hbias : 𝒟[pcF].boolDist 𝒟[pcS] ≤
      expandSAdvantage p prims (expandSDistinguisher p prims hr maxAttempts adv.main) := by
    rw [MeasureTheory.Measure.boolDist, hF, hS]
    exact le_rfl
  -- Assemble: FIPS game ≤ short game + ExpandS ≤ (MLWE + εbridge) + STMSIS + ExpandS.
  have hshort' : 𝒟[pcS] {true} ≤
      LearningWithErrors.advantage mlwe (bridge adv.main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) := by
    rw [← hgS]
    exact hshortBound
  rw [hadv, hgF]
  exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans (add_le_add hshort' hbias)

open scoped Classical in
/-- **NMA security of ML-DSA at the FIPS seed-derived key generation, against seed-based MLWE.**

`nma_security_fips` with no supplied bridge: the MLWE reduction is the short-model key-swap
distinguisher `distinguisherBShort` itself, played against `mldsaMLWEShort`, at zero bridge
slack. For every EUF-NMA adversary `A`,

  `Adv^{EUF-NMA}(A) ≤ Adv^{MLWE-seed}(distinguisherBShort A) + Adv^{SelfTargetMSIS}(C) +
    Adv^{ExpandS}(expandSDistinguisher A)`. -/
theorem nma_security_fips_seed
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGenS : hrS.gen = keygenShort p prims) :
    ∀ (adv : SignatureAlg.EufNmaAdversary
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts)),
    SignatureAlg.eufNmaAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hrS maxAttempts adv.main) +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) +
        expandSAdvantage p prims (expandSDistinguisher p prims hr maxAttempts adv.main) := by
  intro adv
  simpa only [add_zero] using
    nma_security_fips p prims (mldsaMLWEShort p prims) maxAttempts hr hGen hrS hGenS 0
      (distinguisherBShort p prims hrS maxAttempts) (fun _ => le_of_eq (add_zero _).symm) adv

end Headline

end MLDSA
