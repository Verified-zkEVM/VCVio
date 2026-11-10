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
commitment-carrying signature `(w₁, z, h)`.

The NMA bounds hold for forgers that receive the full public key `(ρ, t₁, t₀)`:
`nmaShortAdvantage_keygenShort_le` in the short-key model and `nma_security_fips_full` at the FIPS
seed-derived key generation bound their advantage by MLWE and SelfTargetMSIS advantages, plus the
XOF-replacement term at the FIPS key generation. The reductions hold the full `t` and hand the
forger `t₀`; the SelfTargetMSIS extractor, whose challenge carries only `t₁`, redraws `t₀` from the
fiber of `t₁`. A forger against the scheme itself ignores `t₀`, which gives `nma_security_short`,
`nma_security_short_seed` (the MLWE leg at the seed-based problem, with no supplied bridge) and
`nma_security_fips`. The uniform-matrix MLWE problem is reached in the random-oracle model for
`ExpandA` by `MLDSA.NMA.nma_security_rom` (`LatticeCrypto.MLDSA.SecurityExpandARO`).

The CMA theorems compose the CMA-to-NMA engine with these bounds. They are conditional, and no
instance of them below `1` is proved at a FIPS 204 parameter set, as *Limitations* below explains.
`euf_cma_security_of_nma_short` uses the short-model bound. `euf_cma_security_of_nma_fips` moves a
forger to the scheme with `t₀` in the statement (`unforgeableAdvantage_eq_full`) and uses
`nma_security_fips_full`; `euf_cma_security_of_nma_fips_hvzk` discharges its HVZK hypothesis at
`ζ_zk = 0` with the efficient simulator `hvzkSimulator` (`identificationSchemeFull_perfectHVZK`).

## Limitations

The CMA theorems take hypotheses that are not proved at any FIPS 204 parameter set:

- **`hAbort`, the abort bound.** The response gate passes with probability exactly
  `((2(γ₁ - β) - 1)/(2γ₁))^(256ℓ)` (`prEvent_sampleMaskVec_polyVecNorm_lt`), which is above `1/2` at
  each parameter set. The remaining gates of `respond` read `A·y`, and no lower bound on their pass
  probability is proved.
- **`hGuess`, the commitment-guessing bound.** The only bound proved is `ε = 1`. A useful `ε` needs
  the min-entropy of `HighBits(A·y)` on good keys, for `y` drawn from the mask box.
- **`hhvzk` in the short model.** `euf_cma_security_of_nma_short` runs over
  `identificationSchemeShort`, whose statement `(ρ, t₁)` leaves out the `t₀` the simulator needs,
  and `identificationSchemeFull_perfectHVZK` covers only the seed model. No witness below
  `ζ_zk = 1` is constructed there. The seed model has `ζ_zk = 0`
  (`euf_cma_security_of_nma_fips_hvzk`).

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
  [DecidableEq prims.High] [NeZero p.gamma1]
  {M : Type} [DecidableEq M]
  [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]

/-! ### The EUF-NMA bounds -/

omit nttOps [NeZero p.gamma1] [Inhabited (Commitment p prims)] [Inhabited (Response p prims)] in
/-- Pushing the key generator out of the Fiat-Shamir-with-aborts runtime: a lifted key draw
followed by a random-oracle computation has the measure of the plain `ProbComp` that draws the key
and then simulates the rest from the empty cache. -/
private lemma runtime_evalDist_liftM_keygen_bind
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (rest : PublicKey p prims × SecretKey p →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) Bool) :
    (FiatShamirWithAbort.runtime (Commit := Commitment p prims) (Chal := CommitHashBytes p)
        M).evalDist ((liftM keygen : OracleComp
          (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) _) >>= rest) =
      𝒟[keygen >>= fun ks => simulateToProbComp p prims (M := M) (rest ks)] := by
  let : MeasurableSpace (PublicKey p prims × SecretKey p) := ⊤
  rw [FiatShamirWithAbort.runtime_evalDist_bind_liftComp
    (Commit := Commitment p prims) (Chal := CommitHashBytes p) (M := M),
    evalDist_bind_of_discrete]
  apply Measure.bind_congr_right
  filter_upwards [] with ks
  simpa only [simulateToProbComp, roImpl] using
    (FiatShamirWithAbort.runtime_evalDist_eq_simulateQ_run'
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M (rest ks))

/-- **The short-model NMA game against MLWE and SelfTargetMSIS (Lemma 7, CRYPTO 2023).** For a
forging strategy `main` that receives the full public key `(ρ, t₁, t₀)`, the real-`t` short-model
NMA advantage is at most the `mldsaMLWEShort` advantage of the key-swap distinguisher
`distinguisherBShort` plus the SelfTargetMSIS advantage of the extractor `extractorCShort`.

The key swap is an exact identity (`nma_keyswap_hop_short`), so no statistical slack appears, and
the extractor redraws `t₀` from the fiber of `t₁` (`nmaAdvantage_keygenShort1_le_stmsis`). A
forger against the scheme itself is the case of a `main` that ignores `t₀`
(`nma_security_short`). -/
theorem nmaShortAdvantage_keygenShort_le (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (main : FullPublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    nmaShortAdvantage p prims hr maxAttempts (keygenShort p prims) main ≤
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hr maxAttempts main) +
        SelfTargetMSIS.advantage (extractorCShort p prims main) := by
  set pc0 := (do
      let (pk, sk) ← keygenShort p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← main ⟨pk, sk.t0⟩
        (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpc0
  set pc1 := (do
      let (pk, sk) ← keygenShort1 p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← main ⟨pk, sk.t0⟩
        (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpc1
  have hg0 : nmaShortAdvantage p prims hr maxAttempts (keygenShort p prims) main =
      𝒟[pc0] {true} := by
    rw [nmaShortAdvantage, nmaShortExperiment_eq_keygen_bind]
  have hg1 : nmaShortAdvantage p prims hr maxAttempts (keygenShort1 p prims) main =
      𝒟[pc1] {true} := by
    rw [nmaShortAdvantage, nmaShortExperiment_eq_keygen_bind]
  have hbias : 𝒟[pc0].boolDist 𝒟[pc1] =
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
        (distinguisherBShort p prims hr maxAttempts main) := by
    rw [MeasureTheory.Measure.boolDist, ← hg0, ← hg1]
    exact nma_keyswap_hop_short p prims hr maxAttempts (M := M) main
  have hstm := nmaAdvantage_keygenShort1_le_stmsis p prims hr maxAttempts (M := M) main
  rw [hg1] at hstm
  rw [hg0]
  calc 𝒟[pc0] {true} ≤ 𝒟[pc1] {true} + 𝒟[pc0].boolDist 𝒟[pc1] :=
        MeasureTheory.Measure.apply_true_le_add_boolDist _ _
    _ ≤ SelfTargetMSIS.advantage (extractorCShort p prims main) +
        LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hr maxAttempts main) := by
      rw [hbias]
      exact add_le_add hstm le_rfl
    _ = _ := add_comm _ _

/-- **NMA security of the commitment-carrying ML-DSA signature in the idealized short-key model
(Lemma 7, CRYPTO 2023).**

For every EUF-NMA adversary `A` against the ML-DSA scheme over the idealized short-secret key
generation `keygenShort`, with `A'` the forging strategy that ignores `t₀`
(`fun fpk => A.main fpk.pk`), the MLWE reduction `B = bridge A'` and the SelfTargetMSIS reduction
`C = extractorCShort p prims A'` satisfy

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C)`.

This is `nmaShortAdvantage_keygenShort_le` at `A'`. The reduction `bridge` maps each forging
strategy to an adversary against the abstract MLWE problem `mlwe`, and `hMlweBridge` states that it
is at least as good, up to the slack `εbridge`, as `distinguisherBShort` against the seed-based
short problem `mldsaMLWEShort`, whose secrets are uniform on the `η`-bounded box.
`nma_security_short_seed` takes the bridge to be that problem itself, with no slack; the
uniform-matrix problem is reached by `MLDSA.NMA.nma_security_rom`, which models `ExpandA` as a
random oracle. The pair `(hr, hGen)` is inhabited by `hrShort` (`keygenShort_generable`). -/
theorem nma_security_short {Sample : Type}
    (mlwe : LearningWithErrors.Problem Sample (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGen : hr.gen = keygenShort p prims)
    (εbridge : ℝ≥0∞)
    (bridge : (FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : FullPublicKey p prims →
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
      LearningWithErrors.advantage mlwe (bridge fun fpk => adv.main fpk.pk) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims fun fpk => adv.main fpk.pk) := by
  intro adv
  have hadv : SignatureAlg.eufNmaAdvantage (FiatShamirWithAbort.runtime
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv =
      nmaShortAdvantage p prims hr maxAttempts (keygenShort p prims)
        (fun fpk => adv.main fpk.pk) := by
    rw [SignatureAlg.eufNmaAdvantage, nmaShortAdvantage, nmaShortExperiment]
    rw [SignatureAlg.eufNmaExperiment]
    simp only [FiatShamirWithAbort, hGen]
  rw [hadv]
  exact (nmaShortAdvantage_keygenShort_le p prims maxAttempts hr _).trans
    (add_le_add (hMlweBridge _) le_rfl)

/-- **NMA security of the commitment-carrying ML-DSA signature in the idealized short-key model,
against seed-based MLWE.**

`nma_security_short` with no supplied bridge: the MLWE reduction is the key-swap distinguisher
`distinguisherBShort` itself, played against the seed-based short problem `mldsaMLWEShort`, at
zero bridge slack. For every EUF-NMA adversary `A`, with `A'` the forging strategy that ignores
`t₀`,

  `Adv^{EUF-NMA}(A) ≤ Adv^{MLWE-seed}(distinguisherBShort A') + Adv^{SelfTargetMSIS}(C)`.

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
          (distinguisherBShort p prims hr maxAttempts fun fpk => adv.main fpk.pk) +
        SelfTargetMSIS.advantage (extractorCShort p prims fun fpk => adv.main fpk.pk) := by
  intro adv
  simpa only [add_zero] using
    nma_security_short p prims (mldsaMLWEShort p prims) maxAttempts hr hGen 0
      (distinguisherBShort p prims hr maxAttempts) (fun _ => le_of_eq (add_zero _).symm) adv

/-- The distinguisher of the XOF-replacement hop in `nma_security_fips_full`. On key material
`(ρ, K, s₁, s₂)` it forms `t = ExpandA(ρ)·s₁ + s₂` and runs the EUF-NMA forge-and-verify tail of
`main` at the full public key `(ρ, Power2Round(t))`. In `expandSAdvantage` its real branch is the
EUF-NMA game at the FIPS key generation `keygen0` and its ideal branch the game at `keygenShort`. -/
noncomputable def expandSDistinguisher
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : FullPublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    Bytes 32 → Bytes 32 → RqVec p.l → RqVec p.k → ProbComp Bool :=
  fun rho _key s1 s2 => simulateToProbComp p prims (M := M) (do
    let d ← main ⟨⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩,
      (prims.power2RoundVec (prims.expandA rho * s1 + s2)).2⟩
    (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
      ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2)

omit [Inhabited (Commitment p prims)] [Inhabited (Response p prims)] in
/-- A forger against the seed-model scheme, given `t₀` and ignoring it, has the same EUF-NMA
advantage against the scheme with `t₀` in the statement (key generation `fullRelation hr`): the
verifier ignores `t₀`. -/
theorem eufNmaAdvantage_eq_full
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (adv : SignatureAlg.EufNmaAdversary
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts)) :
    SignatureAlg.eufNmaAdvantage
        (FiatShamirWithAbort.runtime (Commit := Commitment p prims) (Chal := CommitHashBytes p) M)
        adv =
      SignatureAlg.eufNmaAdvantage
        (FiatShamirWithAbort.runtime (Commit := Commitment p prims) (Chal := CommitHashBytes p) M)
        (⟨fun fpk => adv.main fpk.pk⟩ : SignatureAlg.EufNmaAdversary
          (FiatShamirWithAbort (identificationSchemeFull p prims) (fullRelation p prims hr) M
            maxAttempts)) := by
  unfold SignatureAlg.eufNmaAdvantage
  congr 1
  simp only [SignatureAlg.eufNmaExperiment, FiatShamirWithAbort, fullRelation]
  rw [monadLift_map, bind_map_left]
  rfl

/-- **NMA security at the FIPS seed-derived key generation, for forgers that receive `t₀`.**

The short-model bound `nmaShortAdvantage_keygenShort_le` transferred to the deterministic FIPS key
generator `keygen0` through the XOF-replacement hop. For every EUF-NMA adversary `A` against the
scheme with `t₀` in the statement (`identificationSchemeFull`, key generation `fullRelation hr` with
`hGen : hr.gen = keygen0 p prims`), the reductions `B = bridge A.main`,
`C = extractorCShort p prims A.main` and `D = expandSDistinguisher p prims hr maxAttempts A.main`
satisfy

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C) + Adv^{XOF}(D)`,

where `Adv^{XOF}` is `expandSAdvantage`. The FIPS and short games share their forge-and-verify
tail, so their gap is exactly the advantage of `D`, which runs that tail at the key built from the
material `(ρ, K, s₁, s₂)`. -/
theorem nma_security_fips_full {Sample : Type}
    (mlwe : LearningWithErrors.Problem Sample (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (εbridge : ℝ≥0∞)
    (bridge : (FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hrS maxAttempts main) ≤
        LearningWithErrors.advantage mlwe (bridge main) + εbridge) :
    ∀ (adv : SignatureAlg.EufNmaAdversary
      (FiatShamirWithAbort (identificationSchemeFull p prims) (fullRelation p prims hr) M
        maxAttempts)),
    SignatureAlg.eufNmaAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage mlwe (bridge adv.main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) +
        expandSAdvantage p prims (expandSDistinguisher p prims hr maxAttempts adv.main) := by
  classical
  intro adv
  -- The two NMA games as plain `ProbComp`s over their key generators.
  set pcF := (do
      let (pk, sk) ← keygen0 p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← adv.main ⟨pk, sk.t0⟩
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpcF
  set pcS := (do
      let (pk, sk) ← keygenShort p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← adv.main ⟨pk, sk.t0⟩
        (FiatShamirWithAbort (identificationSchemeShort p prims) hrS M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpcS
  have hadv : SignatureAlg.eufNmaAdvantage (FiatShamirWithAbort.runtime
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv = 𝒟[pcF] {true} := by
    rw [SignatureAlg.eufNmaAdvantage, SignatureAlg.eufNmaExperiment]
    simp only [FiatShamirWithAbort, fullRelation, hGen]
    rw [monadLift_map, bind_map_left]
    rw [runtime_evalDist_liftM_keygen_bind p prims (M := M) (keygen0 p prims)]
    refine congrArg (fun μ : Measure Bool => μ {true}) (evalDist_bind_congr _ _ _ fun ks => ?_)
    obtain ⟨pk, sk⟩ := ks
    rfl
  have hgS : 𝒟[pcS] {true} =
      nmaShortAdvantage p prims hrS maxAttempts (keygenShort p prims) adv.main := by
    rw [nmaShortAdvantage, nmaShortExperiment_eq_keygen_bind]
  -- The XOF hop: the two games are the two branches of `expandSDistinguisher`.
  have hF : 𝒟[pcF] {true} = 𝒟[do
      let seed ← $ᵗ (Bytes 32)
      let (rho, rhoPrime, _key) := prims.expandSeed seed
      let (s1, s2) := prims.expandS rhoPrime
      expandSDistinguisher p prims hr maxAttempts adv.main rho _key s1 s2] {true} := by
    rw [hpcF]
    simp only [keygen0, keyFromMaterial, expandSDistinguisher, bind_assoc, pure_bind]
  have hS : 𝒟[pcS] {true} = 𝒟[do
      let key ← $ᵗ (Bytes 32)
      let rho ← $ᵗ (Bytes 32)
      let s1 ← sampleShortVec p.l p.eta
      let s2 ← sampleShortVec p.k p.eta
      expandSDistinguisher p prims hr maxAttempts adv.main rho key s1 s2] {true} := by
    rw [hpcS]
    simp only [keygenShort, keyFromMaterial, expandSDistinguisher, bind_assoc, pure_bind]
    rfl
  have hbias : 𝒟[pcF].boolDist 𝒟[pcS] =
      expandSAdvantage p prims (expandSDistinguisher p prims hr maxAttempts adv.main) := by
    rw [MeasureTheory.Measure.boolDist, hF, hS, expandSAdvantage,
      MeasureTheory.Measure.boolDist]
  have hshort : 𝒟[pcS] {true} ≤
      LearningWithErrors.advantage mlwe (bridge adv.main) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) := by
    rw [hgS]
    exact (nmaShortAdvantage_keygenShort_le p prims maxAttempts hrS adv.main).trans
      (add_le_add (hMlweBridge _) le_rfl)
  rw [hadv]
  exact (MeasureTheory.Measure.apply_true_le_add_boolDist _ _).trans
    (add_le_add hshort hbias.le)

/-- **NMA security of the commitment-carrying ML-DSA signature at the FIPS seed-derived key
generation.** `nma_security_fips_full` at the forging strategy that ignores `t₀`
(`eufNmaAdvantage_eq_full`). The pair `(hr, hGen)` is inhabited by `hrFips`
(`keygen0_generable`). -/
theorem nma_security_fips {Sample : Type}
    (mlwe : LearningWithErrors.Problem Sample (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (εbridge : ℝ≥0∞)
    (bridge : (FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : FullPublicKey p prims →
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
      LearningWithErrors.advantage mlwe (bridge fun fpk => adv.main fpk.pk) + εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims fun fpk => adv.main fpk.pk) +
        expandSAdvantage p prims
          (expandSDistinguisher p prims hr maxAttempts fun fpk => adv.main fpk.pk) := by
  intro adv
  rw [eufNmaAdvantage_eq_full p prims hr maxAttempts adv]
  exact nma_security_fips_full p prims mlwe maxAttempts hr hGen hrS εbridge bridge
    hMlweBridge _

/-! ### The EUF-CMA compositions -/

/-- **EUF-CMA security of the commitment-carrying short-key ML-DSA signature.** Conditional on
`hAbort`, `hGuess` and `hhvzk`, which are not proved at any FIPS 204 parameter set (module
docstring, *Limitations*).

The CMA-to-NMA-to-hardness composition over the idealized short-secret key generation
`keygenShort`: `FiatShamirWithAbort.euf_cma_to_eufNma_of_good_hvzk` bounds the CMA advantage by
the EUF-NMA advantage of the cache-forgetting reduction `simulatedEufNmaAdv` plus
`FiatShamirWithAbort.cmaToNmaLoss`, and `nma_security_short` bounds that EUF-NMA advantage by
MLWE and SelfTargetMSIS, with no key-swap slack. The relation of `hr` is the material-based
`validKeyPairShort`, so `hGen` is inhabited by `hrShort` (`keygenShort_generable`).

**Open: `hhvzk` has no witness below `ζ_zk = 1` so far.** The statement `(ρ, t₁)` of
`identificationSchemeShort` leaves out `t₀`, which the simulator's gates need (module docstring,
*Limitations*). At `ζ_zk = 1` (any simulator, since total variation is at most one) the loss
`FiatShamirWithAbort.cmaToNmaLoss` contains `qS · 1 / (1 − p_abort) ≥ 1` for `qS ≥ 1`.

**Scope: commitment-carrying, not the end-to-end FIPS CMA statement.** FIPS 204 ML-DSA recovers
the commitment at verification; reaching that form costs one extra hash query per signing query,
so the loss moves to `FiatShamirWithAbort.cmaToNmaLoss qS (qH + qS)`. That conversion is not
formalized. -/
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
    (bridge : (FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hr maxAttempts main) ≤
        LearningWithErrors.advantage mlwe (bridge main) + εbridge) :
    SignatureAlg.unforgeableAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage mlwe
          (bridge fun fpk => (FiatShamirWithAbort.simulatedEufNmaAdv
            (identificationSchemeShort p prims) hr M maxAttempts sim adv).main fpk.pk) +
        εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims fun fpk =>
          (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeShort p prims) hr M
            maxAttempts sim adv).main fpk.pk) +
        ENNReal.ofReal
          (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  classical
  have hcma := FiatShamirWithAbort.euf_cma_to_eufNma_of_good_hvzk
    (identificationSchemeShort p prims) hr M maxAttempts sim adv ζ_zk hζ qS qH ε p_abort δ
    hε hδ hp₀ hp Good hGood hhvzk hGuess hAbort hQ
  have hnma := nma_security_short p prims mlwe maxAttempts hr hGen εbridge bridge hMlweBridge
    (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeShort p prims) hr M
      maxAttempts sim adv)
  exact le_trans hcma (add_le_add hnma le_rfl)

/-- **EUF-CMA security of the commitment-carrying ML-DSA signature over seed-derived keys.**
Conditional on `hAbort`, `hGuess` and `hhvzk`, which are not proved at any FIPS 204 parameter set;
`euf_cma_security_of_nma_fips_hvzk` discharges `hhvzk` at `ζ_zk = 0` (module docstring,
*Limitations*).

A forger `adv` against the scheme over `identificationScheme` is a forger against the scheme with
`t₀` in the statement (`unforgeableAdvantage_eq_full`), so the composition runs there:
`FiatShamirWithAbort.euf_cma_to_eufNma_of_good_hvzk` for `identificationSchemeFull` with key
generation `fullRelation hr`, then `nma_security_fips_full`. The HVZK, guessing and abort
hypotheses are about `identificationSchemeFull`, whose commitments and transcripts are those of
`identificationScheme` at `fpk.pk`; the simulator `sim` sees the statement `(ρ, t₁, t₀)`.

**Scope: commitment-carrying, not the end-to-end FIPS CMA statement.** As in the short model, the
signature carries the commitment; the conversion to the FIPS 204 signature format costs `qS` extra
hash queries and is not formalized. -/
theorem euf_cma_security_of_nma_fips {Sample : Type}
    (mlwe : LearningWithErrors.Problem Sample (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (sim : FullPublicKey p prims →
      ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : FullPublicKey p prims → SecretKey p → Prop)
    (hGood : Pr{let xw ← (fullRelation p prims hr).gen}[¬ Good xw.1 xw.2] ≤
      ENNReal.ofReal δ)
    (hhvzk : ∀ fpk sk, validFullKeyPair p prims fpk sk = true → Good fpk sk →
      letI : MeasurableSpace
        (Option (Commitment p prims × CommitHashBytes p × Response p prims)) := ⊤
      measureETVDist ((identificationSchemeFull p prims).honestExecution fpk sk) (sim fpk) ≤
        ENNReal.ofReal ζ_zk)
    (hGuess : ∀ fpk sk, Good fpk sk → ∀ cm : Commitment p prims,
      Pr{let x ← Prod.fst <$> (identificationSchemeFull p prims).commit fpk sk}[x = cm] ≤
        ENNReal.ofReal ε)
    (hAbort : ∀ fpk sk, Good fpk sk →
      Pr{let x ← (identificationSchemeFull p prims).honestExecution fpk sk}[x = none] ≤
        ENNReal.ofReal p_abort)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts))
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims)) (oa := adv.main pk) qS qH)
    (εbridge : ℝ≥0∞)
    (bridge : (FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hrS maxAttempts main) ≤
        LearningWithErrors.advantage mlwe (bridge main) + εbridge) :
    SignatureAlg.unforgeableAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage mlwe
          (bridge (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeFull p prims)
            (fullRelation p prims hr) M maxAttempts sim ⟨fun fpk => adv.main fpk.pk⟩).main) +
        εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims
          (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeFull p prims)
            (fullRelation p prims hr) M maxAttempts sim ⟨fun fpk => adv.main fpk.pk⟩).main) +
        expandSAdvantage p prims (expandSDistinguisher p prims hr maxAttempts
          (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeFull p prims)
            (fullRelation p prims hr) M maxAttempts sim ⟨fun fpk => adv.main fpk.pk⟩).main) +
        ENNReal.ofReal
          (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  classical
  rw [unforgeableAdvantage_eq_full p prims hr maxAttempts adv]
  have hcma := FiatShamirWithAbort.euf_cma_to_eufNma_of_good_hvzk
    (identificationSchemeFull p prims) (fullRelation p prims hr) M maxAttempts sim
    ⟨fun fpk => adv.main fpk.pk⟩ ζ_zk hζ qS qH ε p_abort δ hε hδ hp₀ hp Good hGood hhvzk hGuess
    hAbort (fun fpk => hQ fpk.pk)
  have hnma := nma_security_fips_full p prims mlwe maxAttempts hr hGen hrS εbridge
    bridge hMlweBridge
    (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeFull p prims)
      (fullRelation p prims hr) M maxAttempts sim ⟨fun fpk => adv.main fpk.pk⟩)
  exact le_trans hcma (add_le_add hnma le_rfl)

/-- `euf_cma_security_of_nma_fips` with the HVZK hypothesis discharged at `ζ_zk = 0`. Conditional
on `hAbort` and `hGuess`, which are not proved at any FIPS 204 parameter set (module docstring,
*Limitations*).

Under the primitive laws `h_laws` and `2γ₁ < q`, `identificationSchemeFull_perfectHVZK` makes
`hvzkSimulator` a perfect simulator for `identificationSchemeFull`, so the HVZK term of the loss
vanishes. The simulator reads `t₀`
from the statement and runs in polynomial time, so every reduction here is efficient. -/
theorem euf_cma_security_of_nma_fips_hvzk {Sample : Type}
    (h_laws : Primitives.Laws prims nttOps) (hq : 2 * p.gamma1 < modulus)
    (mlwe : LearningWithErrors.Problem Sample (RqVec p.l) (RqVec p.k))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : FullPublicKey p prims → SecretKey p → Prop)
    (hGood : Pr{let xw ← (fullRelation p prims hr).gen}[¬ Good xw.1 xw.2] ≤
      ENNReal.ofReal δ)
    (hGuess : ∀ fpk sk, Good fpk sk → ∀ cm : Commitment p prims,
      Pr{let x ← Prod.fst <$> (identificationSchemeFull p prims).commit fpk sk}[x = cm] ≤
        ENNReal.ofReal ε)
    (hAbort : ∀ fpk sk, Good fpk sk →
      Pr{let x ← (identificationSchemeFull p prims).honestExecution fpk sk}[x = none] ≤
        ENNReal.ofReal p_abort)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts))
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims)) (oa := adv.main pk) qS qH)
    (εbridge : ℝ≥0∞)
    (bridge : (FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))) →
      LearningWithErrors.Adversary mlwe)
    (hMlweBridge : ∀ (main : FullPublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hrS maxAttempts main) ≤
        LearningWithErrors.advantage mlwe (bridge main) + εbridge) :
    SignatureAlg.unforgeableAdvantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) adv ≤
      LearningWithErrors.advantage mlwe
          (bridge (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeFull p prims)
            (fullRelation p prims hr) M maxAttempts (hvzkSimulator p prims)
            ⟨fun fpk => adv.main fpk.pk⟩).main) +
        εbridge +
        SelfTargetMSIS.advantage (extractorCShort p prims
          (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeFull p prims)
            (fullRelation p prims hr) M maxAttempts (hvzkSimulator p prims)
            ⟨fun fpk => adv.main fpk.pk⟩).main) +
        expandSAdvantage p prims (expandSDistinguisher p prims hr maxAttempts
          (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeFull p prims)
            (fullRelation p prims hr) M maxAttempts (hvzkSimulator p prims)
            ⟨fun fpk => adv.main fpk.pk⟩).main) +
        ENNReal.ofReal (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort 0 δ hp) :=
  euf_cma_security_of_nma_fips p prims mlwe maxAttempts hr hGen hrS
    (hvzkSimulator p prims) 0 le_rfl
    qS qH ε p_abort δ hε hδ hp₀ hp Good hGood
    (fun fpk sk hrel _ => by
      rw [ENNReal.ofReal_zero]
      exact ((identificationSchemeFull p prims).perfectHVZK_iff_hvzk_zero _).mp
        (identificationSchemeFull_perfectHVZK p prims h_laws hq) fpk sk hrel)
    hGuess hAbort adv hQ εbridge bridge hMlweBridge

end Headline

end MLDSA
