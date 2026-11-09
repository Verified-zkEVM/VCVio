/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.MLDSA.SecurityNMA
public import LatticeCrypto.MLDSA.SecurityHVZK

/-!
# ML-DSA EUF-NMA and EUF-CMA headlines

The composed security statements over the reductions of `LatticeCrypto.MLDSA.SecurityNMA`, for the
commitment-carrying signature `(w₁, z, h)`. `nma_security_short` and `nma_security_fips` bound the
EUF-NMA advantage of the short-key and seed-derived schemes by MLWE and SelfTargetMSIS advantages;
`nma_security_short_seed` takes the short-model MLWE leg at the seed-based problem with no supplied
bridge. The uniform-matrix MLWE problem is reached in the random-oracle model for `ExpandA` by
`MLDSA.NMA.nma_security_rom` (`LatticeCrypto.MLDSA.SecurityExpandARO`).

The two CMA theorems compose the CMA-to-NMA engine with these legs. They are conditional, and no
instance of them below `1` is proved at a FIPS 204 parameter set, as *Limitations* below explains.
`euf_cma_security_of_nma_short` uses the short-model NMA leg and `euf_cma_security_of_nma_fips` the
seed-model leg `nma_security_fips`. Both take the simulator and its HVZK error as hypotheses.

## Limitations

The CMA theorems take hypotheses that are not proved at any FIPS 204 parameter set:

- **`hAbort`, the abort bound.** The response gate passes with probability exactly
  `((2(γ₁ - β) - 1)/(2γ₁))^(256ℓ)` (`prEvent_sampleMaskVec_polyVecNorm_lt`), which is above `1/2` at
  each parameter set. The remaining gates of `respond` read `A·y`, and no lower bound on their pass
  probability is proved.
- **`hGuess`, the commitment-guessing bound.** The only bound proved is `ε = 1`. A useful `ε` needs
  the min-entropy of `HighBits(A·y)` on good keys, for `y` drawn from the mask box.
- **`hhvzk`, the HVZK hypothesis.** These theorems are about the signature over
  `identificationScheme`, whose statement `(ρ, t₁)` leaves `t₀` out, and no efficient simulator for
  it is constructed. The efficient perfect simulator is for the variant with `t₀` in the
  statement: `idsWithAbort_hvzk` proves `hvzkSimulator` perfect for `identificationSchemeFull`, and
  `unforgeableAdvantage_eq_full` makes a forger against this signature one against the variant's.
  Composing the two needs the NMA bounds above for forgers that also receive `t₀`. The reductions
  hold the full `t` and can supply it, but those bounds are not stated yet. In the short model the
  same applies, and `idsWithAbort_hvzk` itself covers only the seed model.

The statements also stop short of FIPS 204 in their format and hardness problems:

- **Signature format.** FIPS 204 recovers the commitment at verification. That conversion costs one
  extra hash query per signing query, moving the hash budget of the loss from `qH` to `qH + qS`, and
  it is not formalized.
- **Hardness problems.** The MLWE leg is the seed-based `mldsaMLWEShort`, reached at the
  uniform-matrix problem only in the random-oracle model, and the SelfTargetMSIS leg is the tailored
  `mldsaSTMSISShort` rather than the standard normal form.

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246), Theorems 3 and 4, Lemma 7
- NIST FIPS 204
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

/-- **NMA security of the commitment-carrying ML-DSA signature in the idealized short-key model
(Lemma 7, CRYPTO 2023).**

For every EUF-NMA adversary `A` against the ML-DSA scheme (instantiated via `FiatShamirWithAbort`
over the idealized short-secret key generation `keygenShort`), the MLWE reduction
`B = bridge A.main` and the SelfTargetMSIS reduction `C = extractorCShort p prims A.main` satisfy

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C)`.

The reductions are the concrete ones of `LatticeCrypto.MLDSA.SecurityNMA`: the key-swap
distinguisher `distinguisherBShort`, whose `mldsaMLWEShort` advantage **equals** the real-vs-uniform
key gap —
the short key-swap hop `nma_keyswap_hop_short` is an exact monad identity, so no statistical
slack term appears in the bound — and the SelfTargetMSIS extractor `extractorCShort`, which
turns a uniform-`t` forgery into a short self-target solution
(`nmaAdvantage_keygenShort1_le_stmsis`).

The reduction `bridge` maps each forging strategy to an adversary against the abstract MLWE
problem `mlwe`, and `hMlweBridge` states that it is at least as good, up to the slack `εbridge`, as
`distinguisherBShort` against the seed-based short problem `mldsaMLWEShort` — the
distribution the ML-DSA Module-LWE assumption is stated over (secrets uniform on the `η`-bounded
box). `nma_security_short_seed` instantiates the bridge at that problem itself, with no slack;
the uniform-matrix problem `mldsaMatrixMLWE` is reached by `MLDSA.NMA.nma_security_rom`, which
models `ExpandA` as a random oracle. The SelfTargetMSIS side needs no bridge: the extractor already
targets `mldsaSTMSISShort p prims M`. The hypothesis `hGen : hr.gen = keygenShort p prims` pins the
Fiat-Shamir key generation to the idealized short-key generator. The relation of `hr` is the
material-based `validKeyPairShort`, which `keygenShort` genuinely generates: the pair
`(hr, hGen)` is inhabited by `hrShort` (`keygenShort_generable`), so the statement has
non-vacuous instances.

This is the EUF-NMA half (Lemma 7) of the ML-DSA security proof in the idealized short-key model;
the CMA-to-NMA statistical step (`euf_cma_security_of_nma_short`) composes on top of it. -/
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

/-- **NMA security of the commitment-carrying ML-DSA signature in the idealized short-key model,
against seed-based MLWE.**

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

/-- The distinguisher of the XOF-replacement hop in `nma_security_fips`. On key material
`(ρ, K, s₁, s₂)` it runs the EUF-NMA forge-and-verify tail of `main` at the public key that
`keyFromMaterial` builds from that material. In `expandSAdvantage` its real branch is the EUF-NMA
game at the FIPS key generation `keygen0` and its ideal branch the game at `keygenShort`. -/
noncomputable def expandSDistinguisher
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    Bytes 32 → Bytes 32 → RqVec p.l → RqVec p.k → ProbComp Bool :=
  fun rho _key s1 s2 => simulateToProbComp p prims (M := M) (do
    let d ← main ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩
    (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
      ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2)

/-- **NMA security of the commitment-carrying ML-DSA signature at the FIPS seed-derived key
generation.**

The short-model bound `nma_security_short` transferred to the deterministic FIPS key
generator `keygen0` through the XOF-replacement hop: for every
EUF-NMA adversary against the ML-DSA scheme instantiated with the seed-derived key relation
(`hGen : hr.gen = keygen0 p prims`, inhabited by `hrFips` / `keygen0_generable`), the reductions
`B = bridge A.main` and `C = extractorCShort p prims A.main` satisfy

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C) + Adv^{XOF}(D)`,

where `D = expandSDistinguisher p prims hr maxAttempts A.main` and `Adv^{XOF}` is
`expandSAdvantage`.

The proof has exactly one new ingredient beyond the short model: the FIPS and short NMA
games share their forge-and-verify tail (`identificationScheme` and
`identificationSchemeShort` carry the same `verify` function), so the gap between the
`keygen0` game and the `keygenShort` game is exactly the advantage of `D`, which runs that tail
at the key built by `keyFromMaterial` from the material `(ρ, K, s₁, s₂)`: its real branch is the
FIPS game and its ideal branch is the short game. The short-model reduction hypotheses
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
  -- The PRG hop: the two games are the two branches of `expandSDistinguisher`.
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
    refine le_of_eq ?_
    rw [MeasureTheory.Measure.boolDist, hF, hS, expandSAdvantage,
      MeasureTheory.Measure.boolDist]
    rfl
  -- Assemble: FIPS game ≤ short game + Adv^{XOF}(D) ≤ (MLWE + εbridge) + STMSIS + Adv^{XOF}(D).
  have hshort' : 𝒟[pcS] {true} ≤
      LearningWithErrors.advantage mlwe (bridge adv.main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) := by
    rw [← hgS]
    exact hshortBound
  rw [hadv, hgF]
  exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans (add_le_add hshort' hbias)

/-- **EUF-CMA security of the commitment-carrying short-key ML-DSA signature.** Conditional on
`hAbort`, `hGuess` and `hhvzk`, which are not proved at any FIPS 204 parameter set (module
docstring, *Limitations*).

The CMA-to-NMA-to-hardness composition over the idealized short-secret key generation
`keygenShort`: for any EUF-CMA adversary `adv` against the Fiat-Shamir-with-aborts ML-DSA
signature, the advantage is bounded by the MLWE advantage, the SelfTargetMSIS advantage, and the
statistical CMA-to-NMA loss `FiatShamirWithAbort.cmaToNmaLoss`. The proof composes three pieces:

1. `FiatShamirWithAbort.euf_cma_to_nma`: the CMA advantage is at most the managed-RO NMA
   advantage of `simulatedNmaAdv` plus `FiatShamirWithAbort.cmaToNmaLoss`, under the
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

**Open: `hhvzk` has no witness below `ζ_zk = 1` so far.** The statement `(ρ, t₁)` of
`identificationSchemeShort` leaves out `t₀`, which the simulator's gates need (module docstring,
*Limitations*). At `ζ_zk = 1` (any simulator, since total variation is at most one) the loss
`FiatShamirWithAbort.cmaToNmaLoss` contains `qS · 1 / (1 − p_abort) ≥ 1` for `qS ≥ 1`.

**Scope: commitment-carrying, not the end-to-end FIPS CMA statement.** This theorem is stated for
the standard Fiat-Shamir-with-aborts signature whose commitment is *carried* in the signature (the
generic `Option (Commitment × Response)` type). FIPS 204 ML-DSA instead *recovers* the commitment at
verification; reaching that form costs one extra hash query per signing query, so the loss moves to
`FiatShamirWithAbort.cmaToNmaLoss qS (qH + qS)`. That conversion is not formalized. -/
theorem euf_cma_security_of_nma_short {Sample : Type}
    (mlwe : LearningWithErrors.Problem Sample (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGen : hr.gen = keygenShort p prims)
    (sim : PublicKey p prims →
      ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : PublicKey p prims → SecretKey p → Prop)
    (hGood : Pr{let xw ← hr.gen}[¬ Good xw.1 xw.2] ≤
      ENNReal.ofReal δ)
    (hhvzk : ∀ pk sk, validKeyPairShort p prims pk sk = true → Good pk sk →
      letI : MeasurableSpace
        (Option (Commitment p prims × CommitHashBytes p × Response p prims)) := ⊤
      measureETVDist ((identificationSchemeShort p prims).honestExecution pk sk) (sim pk) ≤
        ENNReal.ofReal ζ_zk)
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
  have hcma := FiatShamirWithAbort.euf_cma_to_eufNma_of_good_hvzk
    (identificationSchemeShort p prims) hr M maxAttempts sim adv ζ_zk hζ qS qH ε p_abort δ
    hε hδ hp₀ hp Good hGood hhvzk hGuess hAbort hQ
  -- Lemma 7, short model: the plain EUF-NMA advantage is bounded by MLWE + STMSIS.
  have hnma := nma_security_short p prims mlwe maxAttempts hr hGen εbridge bridge hMlweBridge
    (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeShort p prims) hr M
      maxAttempts sim adv)
  exact le_trans hcma (add_le_add hnma le_rfl)

/-- **EUF-CMA security of the commitment-carrying ML-DSA signature over seed-derived keys.**
Conditional on `hAbort`, `hGuess` and `hhvzk`, which are not proved at any FIPS 204 parameter set,
`hhvzk` not for any efficient simulator (module docstring, *Limitations*).

The seed-model counterpart of `euf_cma_security_of_nma_short`: the same three-step
composition (`FiatShamirWithAbort.euf_cma_to_nma`, the bridge
`FiatShamirWithAbort.managedRoNmaExperiment_simulatedNmaAdv_eq_eufNmaExperiment`, and the
NMA leg), over the FIPS-shaped key generation `keygen0` and the seed-tagged scheme
`identificationScheme`, with `nma_security_fips` as the NMA leg. Relative to the short model
the bound gains the advantage of `expandSDistinguisher` in the `ExpandS` replacement hop
(`expandSAdvantage`), at the forging strategy of `simulatedEufNmaAdv`; in
exchange the HVZK hypothesis is about the seed-tagged scheme. The efficient perfect simulator of
`idsWithAbort_hvzk` is for its variant with `t₀` in the statement; using it here needs the NMA leg
for forgers that receive `t₀` (module docstring, *Limitations*).

**Scope: commitment-carrying, not the end-to-end FIPS CMA statement.** As in the short model, the
signature carries the commitment; the conversion to the FIPS 204 signature format costs `qS` extra
hash queries and is not formalized. -/
theorem euf_cma_security_of_nma_fips {Sample : Type}
    (mlwe : LearningWithErrors.Problem Sample (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (hGenS : hrS.gen = keygenShort p prims)
    (sim : PublicKey p prims →
      ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : PublicKey p prims → SecretKey p → Prop)
    (hGood : Pr{let xw ← hr.gen}[¬ Good xw.1 xw.2] ≤
      ENNReal.ofReal δ)
    (hhvzk : ∀ pk sk, validKeyPair p prims pk sk = true → Good pk sk →
      letI : MeasurableSpace
        (Option (Commitment p prims × CommitHashBytes p × Response p prims)) := ⊤
      measureETVDist ((identificationScheme p prims).honestExecution pk sk) (sim pk) ≤
        ENNReal.ofReal ζ_zk)
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
        expandSAdvantage p prims (expandSDistinguisher p prims hr maxAttempts
          (FiatShamirWithAbort.simulatedEufNmaAdv (identificationScheme p prims) hr M
            maxAttempts sim adv).main) +
        ENNReal.ofReal
          (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  classical
  -- CMA advantage ≤ plain EUF-NMA advantage of `simulatedEufNmaAdv` + loss.
  have hcma := FiatShamirWithAbort.euf_cma_to_eufNma_of_good_hvzk
    (identificationScheme p prims) hr M maxAttempts sim adv ζ_zk hζ qS qH ε p_abort δ
    hε hδ hp₀ hp Good hGood hhvzk hGuess hAbort hQ
  -- Seed model: the plain EUF-NMA advantage is bounded by MLWE + STMSIS + PRG.
  have hnma := nma_security_fips p prims mlwe maxAttempts hr hGen hrS hGenS εbridge
    bridge hMlweBridge
    (FiatShamirWithAbort.simulatedEufNmaAdv (identificationScheme p prims) hr M
      maxAttempts sim adv)
  exact le_trans hcma (add_le_add hnma le_rfl)

end Headline

end MLDSA
