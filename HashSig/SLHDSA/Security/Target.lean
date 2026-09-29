/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SecretProvider
public import HashSig.SLHDSA.GeneralSchemeQueryBound
public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.Covering

/-!
# SLH-DSA in the random oracle model, and the security target

This module states the random-oracle model in which SLH-DSA's unforgeability is to be bounded,
and the bound.

## The model

Every function FIPS 205 builds from a hash is an oracle query. `hashSpec core` is the whole
interface: the tweakable hash `publicHashSpec core` (`F`, `H`, `T_l` and `H_msg`) beside the
message-randomizer oracle `prfMsgSpec core`. `PRF` is not a separate oracle: FIPS 205's
`PRF(PK.seed, SK.seed, ADRS)` is the tweakable hash at a PRF-typed address applied to `SK.seed`,
so `oracleSecret` draws each WOTS+ and FORS secret as that query, through the equivalence
`e : core.SkSeed ≃ core.Y` that reads the secret seed as a node.

`romScheme core e optRand pkSeedDist` is FIPS 205's internal key generation, signing and
verification (Algorithms 18–20) over `unifSpec + hashSpec core`, on an arbitrary internal message.
Key generation draws the public seed from `pkSeedDist` and the two secret seeds uniformly; signing
draws `opt_rand` from `optRand` (hedged signing draws it uniformly; deterministic signing returns
`PK.seed`, read as a node where the public-seed and node types coincide, as they do at every shipped
bundle), queries `PRF_msg` for the randomizer and signs with every secret drawn from the oracle
(`GeneralScheme.signInternalWithSecretRandomizerM`); verification is `verifyInternalM`.
`romScheme_keygen` and `romScheme_sign` state these as equations: key generation and signing draw
every secret value from `oracleSecret`, and signing draws its randomizer from the `PRF_msg` oracle,
so an adversary learns a secret value only by querying the oracle at a secret seed.

The advantage is VCVio's own `unforgeableAdvantage` under VCVio's own random-oracle runtime
`ProbCompRuntime.rom (hashSpec core)`, from the empty cache. The adversary's budget is
`UnforgeableAdversary.RomQueryBound adv qh qs`: at most `qh` hash queries, `PRF_msg` included, and
at most `qs` signing queries on every path of its own program. The queries key generation, signing
and verification make are not charged; `SignatureAlg.forgerCount_le_of_mem_support_run` counts the
adversary's hash queries on every run of the experiment all the same.

## The target

`SecurityTarget core e optRand c r` bounds the advantage by `securityBound`:
`(qh + 1) · targetCoverBound h a k qs` for the interleaved-target coverage of `H_msg`, and
`(c · qh + qs + (r + 1) · verifyInternalQueryBound) / |Y|` for the events on single oracle
answers. The constants `c` and `r` are fixed numerals at the security theorem; `r` bounds the
honest entries that share one oracle key, and `GeneralScheme.verifyInternalQueryBound` bounds the
verifier's own queries, which a forger can make fire without making any query itself.
`SecurityTarget` is a statement about a given core: it is a security result only at a shipped
bundle with the constants fixed, since at a degenerate core — one whose node type has a single
element, say — the right-hand side reaches one and the target holds trivially.

The target is stated **for each public seed**: its adversaries are those of `romScheme` at
`pkSeedDist := pure pkSeed`. `unforgeableAdvantage_romScheme_le` recovers the bound for every
distribution of the public seed, the uniform one of FIPS 205 included, by averaging over the seed.
The per-seed form is the one a comparison with a single-hash instantiation needs, since whether a
forger-chosen string can also be read as a query of another oracle depends on the public seed.

## Scope

This module states the target; it proves no bound on the advantage. The three-oracle model is the
model the proof works in. The single-SHAKE256 instantiation, in which the tweakable hash, `H_msg`
and `PRF_msg` are one function, is related to it by a separate faithfulness theorem.

## References

* NIST FIPS 205, §9 (Algorithms 18–20), §10.2 (hedged and deterministic signing), §11.1.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA

variable {p : Params}

/-- A query to the message-randomizer function `PRF_msg(SK.prf, opt_rand, M)`. -/
structure PrfMsgQuery (SkPrf Y : Type) where
  /-- The message-randomizer key `SK.prf`. -/
  skPrf : SkPrf
  /-- The optional randomness `opt_rand`. -/
  optRand : Y
  /-- The internal message. -/
  msg : List Byte
deriving DecidableEq

/-- The message-randomizer oracle: `PRF_msg` answers each query with a node. -/
abbrev prfMsgSpec (core : CorePrimitives p) : OracleSpec (PrfMsgQuery core.SkPrf core.Y) :=
  PrfMsgQuery core.SkPrf core.Y →ₒ core.Y

/-- The hash interface of the random-oracle model: the tweakable hash and `H_msg`, beside
`PRF_msg`. `PRF` is the tweakable hash at a PRF-typed address. -/
abbrev hashSpec (core : CorePrimitives p) :
    OracleSpec (PublicHashQuery core.PkSeed core.AdrsKey core.Y ⊕
      PrfMsgQuery core.SkPrf core.Y) :=
  publicHashSpec core + prfMsgSpec core

namespace Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- The secret value at a WOTS+ or FORS secret-key address `a`: `PRF(PK.seed, SK.seed, a)`, which
is the tweakable hash `F` at `a` applied to the secret seed read as a node. -/
@[expose] def oracleSecret (e : core.SkSeed ≃ core.Y) {m : Type → Type*}
    [HasQuery (publicHashSpec core) m] (pkSeed : core.PkSeed) (skSeed : core.SkSeed) :
    Adrs → m core.Y :=
  fun a => PublicHash.f core pkSeed a (e skSeed)

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- FIPS 205 Algorithm 18 at a given public seed, with the secret seeds drawn uniformly and every
secret value drawn from the oracle. -/
@[expose] def romKeygenAt (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed) :
    OracleComp (unifSpec + hashSpec core) (PublicKeyCore core × SecretKeyCore core) := do
  let skSeed ← ($ᵗ core.SkSeed : ProbComp core.SkSeed)
  let skPrf ← ($ᵗ core.SkPrf : ProbComp core.SkPrf)
  let pkRoot ← GeneralScheme.keygenInternalWithSecretM core (oracleSecret core e pkSeed skSeed)
    pkSeed
  return (⟨pkSeed, pkRoot⟩, ⟨skSeed, skPrf, pkSeed, pkRoot⟩)

variable [DecidableEq core.Y]

/-- **SLH-DSA in the random oracle model.** FIPS 205's internal key generation, signing and
verification with every hash, `PRF` and `PRF_msg` included, a query to the oracle. The public seed
is drawn from `pkSeedDist` and `opt_rand` from `optRand`. -/
@[expose] def romScheme (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed) :
    SignatureAlg (OracleComp (unifSpec + hashSpec core)) (List Byte) (PublicKeyCore core)
      (SecretKeyCore core) (GeneralScheme.SignatureCore vp core) where
  keygen := liftM pkSeedDist >>= romKeygenAt core e
  sign pk sk msg := do
    let addrnd ← (optRand pk : ProbComp core.Y)
    let R ← (query (spec := prfMsgSpec core) ⟨sk.skPrf, addrnd, msg⟩ :
      OracleComp (unifSpec + hashSpec core) core.Y)
    GeneralScheme.signInternalWithSecretRandomizerM core (oracleSecret core e sk.pkSeed sk.skSeed)
      msg sk.pkSeed sk.pkRoot R
  verify pk msg sig := GeneralScheme.verifyInternalM vp core msg sig pk

/-- Key generation of `romScheme` draws the public seed, then the two secret seeds, and computes
the root with every secret value drawn from `oracleSecret` at those seeds. -/
theorem romScheme_keygen (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed) :
    (romScheme core e optRand pkSeedDist).keygen = (do
      let pkSeed ← (pkSeedDist : ProbComp core.PkSeed)
      let skSeed ← ($ᵗ core.SkSeed : ProbComp core.SkSeed)
      let skPrf ← ($ᵗ core.SkPrf : ProbComp core.SkPrf)
      let pkRoot ← GeneralScheme.keygenInternalWithSecretM core
        (oracleSecret core e pkSeed skSeed) pkSeed
      return ((⟨pkSeed, pkRoot⟩ : PublicKeyCore core), (⟨skSeed, skPrf, pkSeed, pkRoot⟩ :
        SecretKeyCore core)) : OracleComp (unifSpec + hashSpec core) _) := rfl

/-- Signing of `romScheme` draws `opt_rand`, queries the `PRF_msg` oracle for the randomizer, and
signs with every secret value drawn from `oracleSecret` at the signer's seeds. -/
theorem romScheme_sign (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (pk : PublicKeyCore core) (sk : SecretKeyCore core) (msg : List Byte) :
    (romScheme core e optRand pkSeedDist).sign pk sk msg = (do
      let addrnd ← (optRand pk : ProbComp core.Y)
      let R ← (query (spec := prfMsgSpec core) ⟨sk.skPrf, addrnd, msg⟩ :
        OracleComp (unifSpec + hashSpec core) core.Y)
      GeneralScheme.signInternalWithSecretRandomizerM core
        (oracleSecret core e sk.pkSeed sk.skSeed) msg sk.pkSeed sk.pkRoot R) := rfl

/-- Verification of `romScheme` is FIPS 205 Algorithm 20. -/
theorem romScheme_verify (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (pk : PublicKeyCore core) (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core) :
    (romScheme core e optRand pkSeedDist).verify pk msg sig =
      GeneralScheme.verifyInternalM vp core msg sig pk := rfl

/-- The unforgeability experiment of `romScheme` draws the public seed and then runs the
experiment of `romScheme` at that seed, against the same adversary program. -/
theorem unforgeableExperiment_romScheme (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) :
    unforgeableExperiment adv =
      liftM pkSeedDist >>= fun pkSeed =>
        unforgeableExperiment
          (⟨adv.main⟩ : UnforgeableAdversary (romScheme core e optRand (pure pkSeed))) := by
  simp only [unforgeableExperiment, romScheme, bind_assoc, liftM_pure, pure_bind]
  rfl

/-- The right-hand side of the security target for a node type of `card` elements: the coverage
of the verifier's and the adversary's `H_msg` values, and terms linear in the adversary's hash
queries, its signing queries and the verifier's own queries. -/
@[expose] noncomputable def securityBound (p : Params) (card c r qh qs : ℕ) : ℝ≥0∞ :=
  ((qh : ℝ≥0∞) + 1) * KeyedHash.Covering.targetCoverBound p.h p.a p.k qs +
    ((c : ℝ≥0∞) * qh + qs + ((r + 1) * GeneralScheme.verifyInternalQueryBound p : ℕ)) *
      (card : ℝ≥0∞)⁻¹

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- **The security target** at the constants `c` and `r`: for each public seed, every adversary
against `romScheme` at that seed making at most `qh` hash queries and `qs` signing queries forges
with probability at most `securityBound vp.params |Y| c r qh qs`. -/
@[expose] def SecurityTarget (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (c r : ℕ) : Prop :=
  ∀ (pkSeed : core.PkSeed) (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (qh qs : ℕ), adv.RomQueryBound qh qs →
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
        securityBound vp.params (Nat.card core.Y) c r qh qs

/-- **The target for every distribution of the public seed.** Averaging the per-seed bound over
the seed: an adversary against `romScheme` with the public seed drawn from `pkSeedDist` making at
most `qh` hash queries and `qs` signing queries forges with probability at most
`securityBound vp.params |Y| c r qh qs`. -/
theorem unforgeableAdvantage_romScheme_le {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {c r : ℕ}
    (h : SecurityTarget core e optRand c r) (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) {qh qs : ℕ}
    (hb : adv.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv ≤
      securityBound vp.params (Nat.card core.Y) c r qh qs := by
  let _ : MeasurableSpace core.PkSeed := ⊤
  rw [unforgeableAdvantage, unforgeableExperiment_romScheme,
    ProbCompRuntime.rom_evalDist_bind_liftM,
    Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable]
  calc ∫⁻ pkSeed, (ProbCompRuntime.rom (hashSpec core)).evalDist
          (unforgeableExperiment
            (⟨adv.main⟩ : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))) {true}
          ∂𝒟[pkSeedDist]
      ≤ ∫⁻ _, securityBound vp.params (Nat.card core.Y) c r qh qs ∂𝒟[pkSeedDist] :=
        lintegral_mono fun pkSeed => h pkSeed ⟨adv.main⟩ qh qs hb
    _ = securityBound vp.params (Nat.card core.Y) c r qh qs * 𝒟[pkSeedDist] Set.univ :=
        lintegral_const _
    _ ≤ securityBound vp.params (Nat.card core.Y) c r qh qs :=
        mul_le_of_le_one_right' (evalDist_apply_univ_le_one pkSeedDist)

end Security

end SLHDSA
