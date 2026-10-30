/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.MLDSA.Security
import VCVio.OracleComp.EvalDist.Measure

/-!
# ML-DSA EUF-NMA Security: reduction scaffolding

This file builds the reduction infrastructure for the ML-DSA EUF-NMA analysis:

1. **Exact short-secret MLWE key swap.** `keygenShort` samples `(s₁, s₂)` on the `η`-bounded box
   used by the ML-DSA assumption, while `keygenShort1` replaces `t = Â · s₁ + s₂` by a uniform
   vector. `nma_keyswap_hop_short` identifies their NMA-game gap with the seed-based
   `mldsaMLWEShort` advantage. That problem presents the matrix through a seed for the fixed
   function `prims.expandA`; the uniform-matrix problem `mldsaMatrixMLWE` is reached by modelling
   `ExpandA` as a random oracle in `LatticeCrypto.MLDSA.SecurityExpandARO`.
2. **Seed-derived scaffolding.** `keygen0` and `keygen1` describe the concrete seed-derived and
   uniform-`t` key distributions. The generic lemma `nmaExperiment_eq_keygen_bind` factors either
   key-generator prefix out of the NMA runtime. The older full-ring `mldsaMLWE` definitions remain
   useful scaffolding, but do not identify `keygen0` with a literature MLWE distribution.
3. **SelfTargetMSIS extraction (`nmaAdvantage_keygen1_le_stmsis`).** Once `t` is uniform the key
   carries no secret, so a forgery is a short vector satisfying the *tailored* SelfTargetMSIS
   relation of `mldsaSTMSIS` (see *Tailored vs. standard SelfTargetMSIS* below); the extractor
   `extractorC` reads `(z, c̃)` out of the forged signature. This is fully proven: the
   shared random-oracle simulation lines up the NMA `verify` query with the extractor's RO read-back
   (`stmsis_tail_le`), and an accepted forgery is a valid solution of that problem by commitment
   recoverability.

The `H₁` reprogramming step of the paper folds into the random-oracle modeling and is not separated
out here.

## What is defined here

The honest ML-DSA key distribution embeds an MLWE instance: sample a public seed `ρ`, set the
public matrix `Â = ExpandA(ρ)`, sample short secrets `(s₁, s₂)`, and publish the `Power2Round`
high half of `t = Â · s₁ + s₂`. The uniform-`t` variant replaces `Â · s₁ + s₂` by a uniform
sample. We package both as `ProbComp` key generators, lift each to an EUF-NMA game over an
arbitrary forging adversary `main`, and exhibit the MLWE distinguisher `B` that interpolates
between them: `B (Â, t)` reconstructs the public key from `(ρ, t)` and runs the adversary.

## Modeling note (seeds, not matrices)

The verifier recomputes `Â = ExpandA(pk.ρ)` from the seed stored in the public key, so the MLWE
challenge matrix `Â` must be presented to the adversary *through* a seed `ρ`. Rather than carrying
an embedding witness `ExpandA(ρ) = Â` (which need not exist, since `ExpandA` is not surjective), we
**re-seed-base** the MLWE problem: the public challenge of `mldsaMLWE` is the *seed* `ρ` itself, and
the matrix is *defined* as `Â := ExpandA(ρ)` wherever it is used, so that
`noiseless s₁ ρ = ExpandA(ρ)·s₁`.
This is the standard ROM modeling of Dilithium with `ExpandA` a random oracle, and it makes the
distinguisher `B` total: it consumes `(ρ, t)` and forms `pk = (ρ, Power2Round(t).1)` directly with
no embedding witness required.

## Tailored vs. standard SelfTargetMSIS

The problems `mldsaSTMSIS` and `mldsaSTMSISShort` are **tailored** SelfTargetMSIS problems: their
validity predicate *is* the ML-DSA verifier relation, namely the norm gates `‖z‖∞ < γ₁ − β` and
`weight(h) ≤ ω`, the hint-recovered equation
`w' = UseHint(h, Â·z − SampleInBall(c̃)·(t₁·2^d))` over `R_q`, and the self-target binding
`hashInput.2 = w'` (with the RO consistency of `c̃` supplied by the surrounding
`SelfTargetMSIS.experiment`). What is proved here is the extraction into that tailored problem
together with its algebraic characterization (`stmsisAlgebraicSolution`,
`mldsaSTMSISShort_isValid_iff`, `mldsaSTMSISShort_isValid_expandA_iff`).

This is deliberately *not* the standard SelfTargetMSIS normal form used in the literature, which
states the linear relation as `[I_m | A] · y` with the challenge occupying the final coefficient
block of the short preimage `y`. Reducing the tailored relation to that normal form — absorbing
`UseHint` and the `2^d` shift into a single short vector — is follow-up work, and no declaration
in this file claims it.
-/

@[expose] public section

open MeasureTheory OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

namespace NMA

/-! ## Short-vector sampling -/

/-- `polyVecBounded` is a decidable predicate: it is a `≤` test on the computed
centered infinity norm. -/
instance {k b : ℕ} : DecidablePred (fun v : RqVec k => polyVecBounded v b) := fun _ => by
  unfold polyVecBounded
  exact Nat.decLe _ _

/-- The zero vector lies in every `η`-bounded box. -/
lemma polyVecBounded_zero (k b : ℕ) : polyVecBounded (0 : RqVec k) b := by
  unfold polyVecBounded polyVecNorm
  rw [LatticeCrypto.PolyVec.cInfNorm_le_iff]
  intro j
  have hz : (0 : RqVec k).get j = (0 : Rq) := by
    change (0 : Vector Rq k).get j = 0
    simp [Vector.get]
  rw [hz]
  have h0 : polyNorm (0 : Rq) = 0 := by
    simp only [polyNorm, normOps, LatticeCrypto.zmodPolyNormOps,
      LatticeCrypto.normOpsOfCenteredView, LatticeCrypto.cInfNormOf]
    simp only [vectorNegacyclicRing_backend, vectorBackend_coeff, Finset.sup_eq_zero,
      Finset.mem_univ, Int.natAbs_eq_zero, forall_const]
    intro i
    have hci : Vector.get (0 : Rq) i = (0 : Coeff) :=
      LatticeCrypto.NegacyclicRing.coeff_zero coeffRing i
    rw [hci]
    simp [LatticeCrypto.zmodCenteredCoeffView, LatticeCrypto.centeredRepr]
  calc normOps.cInfNorm (0 : Rq) = polyNorm (0 : Rq) := rfl
    _ = 0 := h0
    _ ≤ b := Nat.zero_le b

/-- **Uniform sampling from the `η`-bounded box.** The uniform distribution on
`S_b^k = { v : RqVec k | ‖v‖∞ ≤ b }`, i.e. every coefficient of every component
uniform on the centered interval `[-b, b]`. This is the secret/error
distribution of the Module-LWE assumption used by ML-DSA (`η ∈ {2, 4}` for the
approved parameter sets). -/
noncomputable def sampleShortVec (k b : ℕ) : ProbComp (RqVec k) :=
  letI : Fintype {v : RqVec k // polyVecBounded v b} := .ofFinite _
  letI : Nonempty {v : RqVec k // polyVecBounded v b} := ⟨0, polyVecBounded_zero k b⟩
  letI : SampleableType {v : RqVec k // polyVecBounded v b} := .ofFintype _
  Subtype.val <$> ($ᵗ {v : RqVec k // polyVecBounded v b})

/-- Every output of `sampleShortVec k b` lies in the `b`-bounded box: the sampler draws from
the subtype `{v // polyVecBounded v b}` and projects out the value, so support membership
carries the bound. -/
lemma mem_support_sampleShortVec {k b : ℕ} {v : RqVec k}
    (hv : v ∈ support (sampleShortVec k b)) : polyVecBounded v b := by
  simp only [sampleShortVec, support_map] at hv
  obtain ⟨u, -, rfl⟩ := hv
  exact u.property

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]

section KeyGen

/-- Build an ML-DSA public/secret key pair from the raw key material
`(ρ, ρ', key, s₁, s₂, t)`, splitting `t` via `Power2Round`. This is the common tail of both the
real and the uniform-`t` key generators: only the *distribution* of `t` differs between them.

When `t = ExpandA(ρ) · s₁ + s₂` this reproduces `keyGenFromSeed` (see `keyFromMaterial_eq`). -/
def keyFromMaterial (rho : Bytes 32) (key : Bytes 32)
    (s1 : RqVec p.l) (s2 : RqVec p.k) (t : RqVec p.k) :
    PublicKey p prims × SecretKey p :=
  let (t1, t0) := prims.power2RoundVec t
  let pk : PublicKey p prims := ⟨rho, t1⟩
  let tr := prims.hashPublicKey rho t1
  let sk : SecretKey p := ⟨rho, key, tr, s1, s2, t0⟩
  (pk, sk)

/-- **Game 0 key generation (real `t`).** Sample a seed, expand it into `(ρ, ρ', key)` and the
secrets `(s₁, s₂)`, then form the key from `t = ExpandA(ρ) · s₁ + s₂`. This is `keyGenFromSeed`
phrased as a `ProbComp` over the uniform seed distribution. -/
def keygen0 : ProbComp (PublicKey p prims × SecretKey p) := do
  let seed ← $ᵗ (Bytes 32)
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let (s1, s2) := prims.expandS rhoPrime
  let t := prims.expandA rho * s1 + s2
  return keyFromMaterial p prims rho key s1 s2 t

/-- **Game 1 key generation (uniform `t`).** Identical to `keygen0` except the public vector `t`
is sampled uniformly instead of being computed as `ExpandA(ρ) · s₁ + s₂`. This is the
intermediate game used in the first hop of Lemma 7. -/
def keygen1 : ProbComp (PublicKey p prims × SecretKey p) := do
  let seed ← $ᵗ (Bytes 32)
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let (s1, s2) := prims.expandS rhoPrime
  let t ← $ᵗ (RqVec p.k)
  return keyFromMaterial p prims rho key s1 s2 t

/-- `keyFromMaterial` reproduces `keyGenFromSeed` on the honest material derived from a seed. -/
theorem keyFromMaterial_eq (seed : Bytes 32) :
    let (rho, rhoPrime, key) := prims.expandSeed seed
    let (s1, s2) := prims.expandS rhoPrime
    keyFromMaterial p prims rho key s1 s2 (prims.expandA rho * s1 + s2) =
      keyGenFromSeed p prims seed := by
  simp only [keyFromMaterial, keyGenFromSeed]

/-! ### Short-secret sampling and the idealized key generators

The FIPS key generator derives everything deterministically from one seed
(`keygen0` above). The idealized proof-level model instead samples the matrix
seed `ρ`, the signing key `K`, and the short secrets `(s₁, s₂)` independently,
with `(s₁, s₂)` uniform on the `η`-bounded box `S_η^ℓ × S_η^k` — the
distribution the Module-LWE assumption for ML-DSA is stated over. The key-swap
hop is then an exact monad identity against `mldsaMLWEShort` (no statistical
slack); the deterministic-XOF derivation is not part of this hop and is charged
separately as the `expandSAdvantage` of a named distinguisher. -/

/-- **Idealized key generation (real `t`).** Sample the matrix seed `ρ`, the
signing key `K`, and the short secrets `(s₁, s₂)` independently — `(s₁, s₂)`
uniform on the `η`-bounded box — and form `t = ExpandA(ρ) · s₁ + s₂`. This is
the honestly-sampled key distribution of the idealized proof-level ML-DSA
model; the deterministic seed-expanded `keygen0` is related to it by the `ExpandS`
replacement game (`expandSAdvantage`). -/
noncomputable def keygenShort : ProbComp (PublicKey p prims × SecretKey p) := do
  let key ← $ᵗ (Bytes 32)
  let rho ← $ᵗ (Bytes 32)
  let s1 ← sampleShortVec p.l p.eta
  let s2 ← sampleShortVec p.k p.eta
  let t := prims.expandA rho * s1 + s2
  return keyFromMaterial p prims rho key s1 s2 t

/-- **Idealized key generation (uniform `t`).** Identical to `keygenShort`
except the public vector `t` is sampled uniformly. The gap between the two is
exactly the `mldsaMLWEShort` distinguishing advantage of the induced
distinguisher (`nma_keyswap_hop_short`). -/
noncomputable def keygenShort1 : ProbComp (PublicKey p prims × SecretKey p) := do
  let key ← $ᵗ (Bytes 32)
  let rho ← $ᵗ (Bytes 32)
  let s1 ← sampleShortVec p.l p.eta
  let s2 ← sampleShortVec p.k p.eta
  let t ← $ᵗ (RqVec p.k)
  return keyFromMaterial p prims rho key s1 s2 t

/-- The generable relation carried by the idealized short-key model: the generator is
`keygenShort`, and every generated pair is material-valid. Each pair drawn by `keygenShort`
is literally `keyFromMaterial ρ K s₁ s₂ (ExpandA(ρ)·s₁ + s₂)` for uniform `ρ`, `K` and
box-sampled `(s₁, s₂)`, and `sampleShortVec` outputs are `η`-bounded on their support
(`mem_support_sampleShortVec`) — exactly the witness `validKeyPairShort` asks for. This
inhabits the `hGen` hypothesis of the short-model security headlines
(`keygenShort_generable`). -/
noncomputable def hrShort :
    GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims) :=
  ⟨keygenShort p prims, fun pk sk hmem => by
    rw [validKeyPairShort_eq_true_iff]
    simp only [keygenShort, mem_support_bind_iff] at hmem
    obtain ⟨key, -, rho, -, s1, hs1, s2, hs2, hpure⟩ := hmem
    refine ⟨rho, key, s1, s2, mem_support_sampleShortVec hs1,
      mem_support_sampleShortVec hs2, ?_⟩
    simpa only [keyFromMaterial] using (eq_of_mem_support_pure _ hpure).symm⟩

/-- **Satisfiability certificate for the short-model `hGen` hypothesis.** Some generable
relation over `validKeyPairShort` has `keygenShort` as its generator — witnessed by
`hrShort`. The short-model security statements hypothesize such a relation via
`hGen : hr.gen = keygenShort p prims`; this theorem records that the hypothesis pair
`(hr, hGen)` is inhabited, so those statements have non-vacuous instances. -/
theorem keygenShort_generable :
    ∃ hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims),
      hr.gen = keygenShort p prims :=
  ⟨hrShort p prims, rfl⟩

/-- The generable relation carried by the FIPS seed-derived key generation: the generator is
`keygen0`, and every generated pair is seed-valid. Each pair drawn by `keygen0` is literally
the key assembled by `keyFromMaterial` from the material expanded out of its seed, which
`keyFromMaterial_eq` identifies with `keyGenFromSeed` — exactly the witness `validKeyPair`
asks for. This inhabits the `hGen` hypothesis of the FIPS-keygen security corollary
(`keygen0_generable`). -/
def hrFips :
    GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims) :=
  ⟨keygen0 p prims, fun pk sk hmem => by
    rw [validKeyPair_eq_true_iff]
    simp only [keygen0, mem_support_bind_iff] at hmem
    obtain ⟨seed, -, hpure⟩ := hmem
    refine ⟨seed, ?_⟩
    have h := (eq_of_mem_support_pure _ hpure).symm
    simpa only [keyFromMaterial, keyGenFromSeed] using h⟩

/-- **Satisfiability certificate for the FIPS-keygen `hGen` hypothesis.** Some generable
relation over `validKeyPair` has the seed-derived FIPS key generator `keygen0` as its
generator — witnessed by `hrFips`. The FIPS-keygen security corollary hypothesizes such a
relation via `hGen : hr.gen = keygen0 p prims`; this theorem records that the hypothesis
pair `(hr, hGen)` is inhabited, so that statement has non-vacuous instances. -/
theorem keygen0_generable :
    ∃ hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims),
      hr.gen = keygen0 p prims :=
  ⟨hrFips p prims, rfl⟩

/-- **Real branch of the `ExpandS` replacement game.** Expand a uniform 32-byte seed into
`(ρ, ρ', K)`, derive `(s₁, s₂) = ExpandS(ρ')`, and run the distinguisher `D` on
`(ρ, K, s₁, s₂)`: the key material that the FIPS key generator `keygen0` uses. -/
def expandSRealExperiment (D : Bytes 32 → Bytes 32 → RqVec p.l → RqVec p.k → ProbComp Bool) :
    ProbComp Bool := do
  let seed ← $ᵗ (Bytes 32)
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let (s1, s2) := prims.expandS rhoPrime
  D rho key s1 s2

/-- **Ideal branch of the `ExpandS` replacement game.** Sample `K` and `ρ` uniformly and
`(s₁, s₂)` uniformly on the `η`-bounded box `S_η^ℓ × S_η^k`, and run the distinguisher `D` on
`(ρ, K, s₁, s₂)`: the key material that the idealized key generator `keygenShort` uses. -/
noncomputable def expandSIdealExperiment
    (D : Bytes 32 → Bytes 32 → RqVec p.l → RqVec p.k → ProbComp Bool) : ProbComp Bool := do
  let key ← $ᵗ (Bytes 32)
  let rho ← $ᵗ (Bytes 32)
  let s1 ← sampleShortVec p.l p.eta
  let s2 ← sampleShortVec p.k p.eta
  D rho key s1 s2

/-- **Distinguishing advantage against the `ExpandS` replacement.** The Boolean distance between
`expandSRealExperiment D` and `expandSIdealExperiment D`: how well `D` tells the FIPS derivation
of `(ρ, K, s₁, s₂)` from one seed through `ExpandSeed`/`ExpandS` apart from independent sampling
with the short-box marginals of `keygenShort`.

`nma_security_fips` charges this advantage for the single named distinguisher
`expandSDistinguisher` its proof builds, not for every distinguisher. Over all distinguishers the
supremum is close to `1`, since an unbounded `D` can test membership in the image of the
`2^256`-point seed expansion. For that named distinguisher, whose cost is that of one run of the
forger plus verification, the advantage is the quantity a PRG assumption on the SHAKE-based
expansion bounds; no cost model is attached here (#460). -/
noncomputable def expandSAdvantage
    (D : Bytes 32 → Bytes 32 → RqVec p.l → RqVec p.k → ProbComp Bool) : ℝ≥0∞ :=
  𝒟[expandSRealExperiment p prims D].boolDist 𝒟[expandSIdealExperiment p prims D]

end KeyGen

section Game

variable {M : Type} [DecidableEq M] [SampleableType (CommitHashBytes p)] [DecidableEq prims.High]

/-- The EUF-NMA experiment over an arbitrary forging strategy `main` and an arbitrary key
generator `keygen`. `main` receives the public key (but no signing oracle) and returns a candidate
`(message, signature)`; the experiment outputs the validity bit of the forgery.

Specializing `keygen` to `keygen0` / `keygen1` gives the seed-derived / uniform-`t` NMA
experiments used by the extraction scaffolding. The signature scheme is the ML-DSA
`FiatShamirWithAbort (identificationScheme …)`, so `verify` recomputes `Â = ExpandA(pk.ρ)` from the
published seed. The exact MLWE key-swap theorem below instead uses the corresponding short-secret
experiment `nmaShortExperiment`. -/
noncomputable def nmaExperiment
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) Bool := do
  let (pk, _) ← (liftM keygen : OracleComp
    (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) _)
  let (msg, σ) ← main pk
  (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ

/-- The advantage of the NMA experiment with key generator `keygen` is its `true`-probability in
the Fiat-Shamir-with-aborts runtime. -/
noncomputable def nmaAdvantage
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) : ℝ≥0∞ :=
  (FiatShamirWithAbort.runtime (Commit := Commitment p prims) (Chal := CommitHashBytes p)
    M).evalDist (nmaExperiment p prims hr maxAttempts keygen main) {true}

/-! ### Short-model EUF-NMA game -/

/-- The EUF-NMA experiment over the idealized short-key scheme: identical to `nmaExperiment` except
the signature scheme is `FiatShamirWithAbort` over `identificationSchemeShort`, whose key relation
`validKeyPairShort` is the material-based one that `keygenShort` generates (`hrShort`). The forging
interface and the verify recomputation are unchanged. -/
noncomputable def nmaShortExperiment
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) Bool := do
  let (pk, _) ← (liftM keygen : OracleComp
    (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) _)
  let (msg, σ) ← main pk
  (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify pk msg σ

/-- The advantage of the short-model NMA experiment with key generator `keygen` is its
`true`-probability in the Fiat-Shamir-with-aborts runtime. The exact short hop identifies
`|nmaShortAdvantage keygenShort − nmaShortAdvantage keygenShort1|` with the `mldsaMLWEShort`
advantage of `distinguisherBShort`. -/
noncomputable def nmaShortAdvantage
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) : ℝ≥0∞ :=
  (FiatShamirWithAbort.runtime (Commit := Commitment p prims) (Chal := CommitHashBytes p)
    M).evalDist (nmaShortExperiment p prims hr maxAttempts keygen main) {true}

end Game

section Distinguisher

variable {M : Type} [DecidableEq M] [SampleableType (CommitHashBytes p)] [DecidableEq prims.High]

/-- The random-oracle simulation implementation used by `FiatShamirWithAbort.runtime`: the
random oracle model handler `OracleSpec.romImpl` at the ML-DSA commitment-hash oracle. Running
an oracle computation through this implementation and projecting away the final cache turns it
into a plain `ProbComp`, which is what the MLWE distinguisher must return. -/
def roImpl :
    QueryImpl (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp) :=
  (M × Commitment p prims →ₒ CommitHashBytes p).romImpl

/-- Observe an oracle computation as a plain `ProbComp` by simulating its random oracle from an
empty cache and discarding the final cache state. This is exactly the `ProbComp` underlying
`FiatShamirWithAbort.runtime.evalDist`, exposed so the
MLWE distinguisher — which must inhabit `… → ProbComp Bool` — can run the NMA game internally. -/
def simulateToProbComp {α : Type}
    (mx : OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) α) :
    ProbComp α :=
  StateT.run' (simulateQ (roImpl p prims (M := M)) mx) ∅

/-- The concrete MLWE problem embedded by ML-DSA key generation, **seed-based**: the public
challenge is the public matrix seed `ρ = (ExpandSeed(seed)).1` for a uniform `seed`, the secret is
`s₁`, and the output is `t`. The matrix is recovered on demand as `Â := ExpandA(ρ)`, so
`noiseless s₁ ρ = ExpandA(ρ) · s₁`; the secret and error/uniform distributions are uniform.

Sampling `ρ` through `ExpandSeed` (rather than uniformly) makes the `ρ` marginal line up exactly
with `keygen0` / `keygen1`, so the uniform branch against `keygen1` is a clean monad-rewriting
fact. The real branch is intentionally not identified with `keygen0`: here `s₁` and the error are
independent uniform elements of the full ring, whereas `keygen0` derives `η`-bounded vectors from
the same seed as `ρ`. No random-oracle assumption turns those distributions into one another.
The short-secret problem `mldsaMLWEShort` below is the literature-facing formulation used by the
proved key-swap theorem.

The matrix never appears as a free challenge: phrasing the MLWE instance over seeds is exactly the
ROM modeling of Dilithium with `ExpandA` a random oracle, and it makes the distinguisher `B` total
(no `ExpandA`-surjectivity assumption). Relating an abstract matrix-based MLWE problem to this
concrete seed-based one is a statement-level bridge obligation. -/
def mldsaMLWE (p : Params) (prims : Primitives p) :
    LearningWithErrors.Problem (Bytes 32) (RqVec p.l) (RqVec p.k) where
  sampleChallenge := do
    let seed ← $ᵗ (Bytes 32)
    return (prims.expandSeed seed).1
  sampleSecret := $ᵗ (RqVec p.l)
  sampleError := $ᵗ (RqVec p.k)
  noiseless := fun s1 rho => prims.expandA rho * s1
  sampleUniform := $ᵗ (RqVec p.k)

/-- **The MLWE distinguisher `B`.** Given a seed-based MLWE challenge `(ρ, t)` (real
`ExpandA(ρ)·s₁ + s₂` vs uniform `t`), `B` forms the ML-DSA public key `pk = (ρ, Power2Round(t).1)`
directly from the seed, runs the NMA forging strategy `main` on `pk`, simulates the random oracle
to verify the returned forgery, and outputs the validity bit as its decision.

The uniform branch reproduces `nmaExperiment … keygen1`. The full-ring real branch does **not**
reproduce `keygen0`: this problem samples `s₁` and `s₂` independently and uniformly over the
entire ring, whereas `keygen0` derives `η`-bounded secrets from the same seed as `ρ`. Accordingly,
this definition is retained as seed-based reduction scaffolding rather than a proved key-swap hop.
The live exact hop uses `mldsaMLWEShort` and `distinguisherBShort` below. -/
noncomputable def distinguisherB
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    LearningWithErrors.Adversary (mldsaMLWE p prims) :=
  fun (challenge : Bytes 32 × RqVec p.k) =>
    let rho := challenge.1
    let t := challenge.2
    let pk : PublicKey p prims := ⟨rho, (prims.power2RoundVec t).1⟩
    simulateToProbComp p prims (M := M) do
      let (msg, σ) ← main pk
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ

/-! ### Short-secret MLWE problems

The idealized short-key model states its Module-LWE assumption over short `(s₁, s₂)`
(`mldsaMLWEShort`, seed-based; `mldsaMatrixMLWE`, uniform-matrix form). For the fixed function
`prims.expandA` no bound of the seed-based problem by the uniform-matrix one is available: a
distinguisher receiving `(ρ, Â)` can recompute `ExpandA(ρ)` and compare. The uniform-matrix
problem is reached by `MLDSA.NMA.nma_security_rom`, which models `ExpandA` as a random oracle.
`distinguisherBShort` is the induced distinguisher whose advantage the short key-swap hop
bounds. -/

/-- **The short-secret Module-LWE problem for ML-DSA** (seed-based form). The public
challenge is the matrix seed `ρ` itself (uniform), the secret `s₁` and the additive
error `s₂` are uniform on the `η`-bounded box (`sampleShortVec`), and the decision
target is `t = ExpandA(ρ) · s₁ + s₂` versus uniform `t`. This is the distribution the
ML-DSA literature states its MLWE assumption over; unlike a uniform-error variant it
is not information-theoretically trivial, since `ExpandA(ρ) · s₁ + s₂` with short
`(s₁, s₂)` is far from uniform. The uniform-matrix form `mldsaMatrixMLWE` is reached by
`MLDSA.NMA.nma_security_rom`, which models `ExpandA` as a random oracle. -/
noncomputable def mldsaMLWEShort (p : Params) (prims : Primitives p) :
    LearningWithErrors.Problem (Bytes 32) (RqVec p.l) (RqVec p.k) where
  sampleChallenge := $ᵗ (Bytes 32)
  sampleSecret := sampleShortVec p.l p.eta
  sampleError := sampleShortVec p.k p.eta
  noiseless := fun s1 rho => prims.expandA rho * s1
  sampleUniform := $ᵗ (RqVec p.k)

/-- **The matrix-based short Module-LWE problem for ML-DSA.** The standard form: the
public challenge is a uniform matrix `A`, the secret and error are uniform on the
`η`-bounded box, and the decision target is `A · s₁ + s₂` versus uniform. This is the
literature-facing hardness assumption; `MLDSA.NMA.nma_security_rom` reaches it by modelling
`ExpandA` as a random oracle. -/
noncomputable def mldsaMatrixMLWE (p : Params) :
    LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k) where
  sampleChallenge := $ᵗ (TqMatrix p.k p.l)
  sampleSecret := sampleShortVec p.l p.eta
  sampleError := sampleShortVec p.k p.eta
  noiseless := fun s1 A => A * s1
  sampleUniform := $ᵗ (RqVec p.k)

/-- The short-model MLWE distinguisher: form `pk = (ρ, Power2Round(t).1)` from the challenge
`(ρ, t)`, run the NMA forging strategy
`main` on `pk`, simulate the random oracle to verify the returned forgery, and output the
validity bit — typed against the short-secret problem `mldsaMLWEShort` and the short-key
scheme `identificationSchemeShort`. When `(ρ, t)` is real it reproduces
`nmaShortExperiment … keygenShort`; when `t` is uniform it reproduces
`nmaShortExperiment … keygenShort1` (`nma_keyswap_hop_short`). -/
noncomputable def distinguisherBShort
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    LearningWithErrors.Adversary (mldsaMLWEShort p prims) :=
  fun (challenge : Bytes 32 × RqVec p.k) =>
    let rho := challenge.1
    let t := challenge.2
    let pk : PublicKey p prims := ⟨rho, (prims.power2RoundVec t).1⟩
    simulateToProbComp p prims (M := M) do
      let (msg, σ) ← main pk
      (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify pk msg σ

/-- **The `ExpandS` replacement distinguisher.** On key material `(ρ, K, s₁, s₂)` it forms the
public key `pk = (ρ, Power2Round(ExpandA(ρ)·s₁ + s₂).1)` that `keyFromMaterial` builds from that
material, runs the NMA forging strategy `main` on `pk`, verifies the returned forgery through the
signature's runtime, and outputs the validity bit. On the real branch
(`expandSRealExperiment`) it reproduces the NMA game at the FIPS key generator `keygen0`; on the
ideal branch (`expandSIdealExperiment`) it reproduces the NMA game at `keygenShort`. -/
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

end Distinguisher

section Hop

variable {M : Type} [DecidableEq M] [SampleableType (CommitHashBytes p)] [DecidableEq prims.High]

/-- **NMA-game / distinguisher plumbing.** Pushing the `keygen` sampling out of the
Fiat-Shamir-with-aborts runtime: the output measure of `nmaExperiment … keygen` equals that of
first sampling `(pk, _) ← keygen` (in plain `ProbComp`) and then running the forge-and-verify tail
through `simulateToProbComp` — which is exactly the body of `distinguisherB` evaluated at `pk`.

This is the bundled-semantics fact that `runtime.evalDist (liftM oa >>= rest)` is the measure bind
of `𝒟[oa]` with the runtime measures of the continuations, specialised to
the ML-DSA NMA game. It discharges the runtime plumbing but deliberately makes no claim that two
different key distributions coincide. -/
theorem nmaExperiment_eq_keygen_bind
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    (FiatShamirWithAbort.runtime (Commit := Commitment p prims) (Chal := CommitHashBytes p)
        M).evalDist (nmaExperiment p prims hr maxAttempts keygen main) =
      𝒟[(do
        let (pk, _) ← keygen
        simulateToProbComp p prims (M := M) (do
          let (msg, σ) ← main pk
          (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
            pk msg σ))] := by
  let : MeasurableSpace (PublicKey p prims × SecretKey p) := ⊤
  let rest : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) Bool := fun pk => do
    let (msg, σ) ← main pk
    (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ
  unfold nmaExperiment
  rw [FiatShamirWithAbort.runtime_evalDist_bind_liftComp
    (Commit := Commitment p prims) (Chal := CommitHashBytes p) (M := M),
    evalDist_bind_of_discrete]
  apply Measure.bind_congr_right
  filter_upwards [] with pk
  simpa only [simulateToProbComp, roImpl] using
    (FiatShamirWithAbort.runtime_evalDist_eq_simulateQ_run'
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M (rest pk.1))

/-! ### The exact short-model key-swap hop -/

/-- Short-model NMA-game / distinguisher plumbing: the `nmaExperiment_eq_keygen_bind` rewrite at the
short scheme. Pushing the `keygen` sampling out of the Fiat-Shamir-with-aborts runtime, the
output measure of `nmaShortExperiment … keygen` equals that of first sampling `(pk, _) ← keygen`
in plain `ProbComp` and then running the forge-and-verify tail through `simulateToProbComp` —
exactly the body of `distinguisherBShort` evaluated at `pk`. -/
theorem nmaShortExperiment_eq_keygen_bind
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    (FiatShamirWithAbort.runtime (Commit := Commitment p prims) (Chal := CommitHashBytes p)
        M).evalDist (nmaShortExperiment p prims hr maxAttempts keygen main) =
      𝒟[(do
        let (pk, _) ← keygen
        simulateToProbComp p prims (M := M) (do
          let (msg, σ) ← main pk
          (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify
            pk msg σ))] := by
  let : MeasurableSpace (PublicKey p prims × SecretKey p) := ⊤
  let rest : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) Bool := fun pk => do
    let (msg, σ) ← main pk
    (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify pk msg σ
  unfold nmaShortExperiment
  rw [FiatShamirWithAbort.runtime_evalDist_bind_liftComp
    (Commit := Commitment p prims) (Chal := CommitHashBytes p) (M := M),
    evalDist_bind_of_discrete]
  apply Measure.bind_congr_right
  filter_upwards [] with pk
  simpa only [simulateToProbComp, roImpl] using
    (FiatShamirWithAbort.runtime_evalDist_eq_simulateQ_run'
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M (rest pk.1))

/-- **The exact short-model key-swap hop.** Against the idealized key generators
`keygenShort` / `keygenShort1`, the short-model NMA-game gap **is** the `mldsaMLWEShort`
distinguishing advantage of `distinguisherBShort` — both branch identifications are pure
monad-rewriting identities, with no statistical slack: the key generators sample
`ρ`, `K`, `s₁`, `s₂` independently, exactly as the problem's `distr`/`uniformDistr`
do (the unused `K` draw strips off, being the leading draw).

Proof recipe: both branches follow the same shape: `rw [nmaShortExperiment_eq_keygen_bind]`,
`simp only [LearningWithErrors.realExperiment/randomExperiment,
LearningWithErrors.distr/uniformDistr, distinguisherBShort, mldsaMLWEShort, keygenShort/1,
keyFromMaterial, bind_assoc, pure_bind]`,
strip unused lossless draws with `OracleComp.evalDist_bind_const`, and
close by simplifying the resulting plain `ProbComp` bind. -/
theorem nma_keyswap_hop_short
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    ENNReal.absDiff (nmaShortAdvantage p prims hr maxAttempts (keygenShort p prims) main)
        (nmaShortAdvantage p prims hr maxAttempts (keygenShort1 p prims) main) =
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
        (distinguisherBShort p prims hr maxAttempts main) := by
  set B := distinguisherBShort p prims hr maxAttempts main (M := M) with hB
  rw [NoisyLearning.advantage_eq_boolDist (mldsaMLWEShort p prims) B,
    MeasureTheory.Measure.boolDist]
  have hH1 : nmaShortAdvantage p prims hr maxAttempts (keygenShort1 p prims) main =
      𝒟[LearningWithErrors.randomExperiment (mldsaMLWEShort p prims) B] {true} := by
    rw [nmaShortAdvantage, nmaShortExperiment_eq_keygen_bind]
    simp only [LearningWithErrors.randomExperiment, LearningWithErrors.uniformDistr, hB,
      distinguisherBShort, mldsaMLWEShort, keygenShort1, keyFromMaterial, bind_assoc, pure_bind]
    -- Strip the unused leading `key` draw, then the unused `s₁`, `s₂` draws under `ρ`.
    rw [OracleComp.evalDist_bind_const]
    apply congrArg (fun μ : Measure Bool => μ {true})
    refine evalDist_bind_congr _ _ _ fun rho => ?_
    rw [OracleComp.evalDist_bind_const, OracleComp.evalDist_bind_const]
  have hH0 : nmaShortAdvantage p prims hr maxAttempts (keygenShort p prims) main =
      𝒟[LearningWithErrors.realExperiment (mldsaMLWEShort p prims) B] {true} := by
    rw [nmaShortAdvantage, nmaShortExperiment_eq_keygen_bind]
    simp only [LearningWithErrors.realExperiment, LearningWithErrors.distr, hB, distinguisherBShort,
      mldsaMLWEShort, keygenShort, keyFromMaterial, bind_assoc, pure_bind]
    -- Only the leading `key` draw is unused here (`s₁`, `s₂` build `t`).
    rw [OracleComp.evalDist_bind_const]
  rw [hH0, hH1]

end Hop

/-! ## The verifier's recomputation in coefficient form -/

/-- Under the transform laws, the verifier's recomputation `computeWApprox` is the plain
coefficient-domain matrix expression `Â·z − c·(t₁·2^d)`: the transform round trip
disappears, `*`/`•` are the transform-backed matrix-vector and scalar-vector products on
`R_q`, and `t₁·2^d = power2RoundShiftVec t₁`. Only the transform-isomorphism laws are
consumed (`unhatVec_sub`); both summands are definitionally the coefficient-domain
products. -/
theorem computeWApprox_eq_mul_sub_smul (h_transform : NTTRingLaws nttOps)
    (aHat : TqMatrix p.k p.l) (c : ChallengePoly) (z : RqVec p.l)
    (t1 : Vector prims.Power2High p.k) :
    computeWApprox p prims aHat c z t1 =
      aHat * z - c • prims.power2RoundShiftVec t1 := by
  have := h_transform
  simp only [computeWApprox]
  exact nttOps.unhatVec_sub _ _

section Extractor

variable {M : Type} [DecidableEq prims.High]

/-- The concrete SelfTargetMSIS problem embedded by ML-DSA verification (Lemma 7, Step 3).

After the key has uniform `t` (`keygen1`), a forgery `(msg, some (w', (z, h)))` accepted by
`verify` is, via the random oracle answer `c̃ = H(msg, w')`, a SelfTargetMSIS solution: the matrix
`Â = ExpandA(ρ)` is the challenge, the public key `pk` is the target, the hash input is `(msg, w')`,
and the response is `(z, h)`. Validity recomputes the commitment from `(pk, c̃, (z, h))` via
`UseHint ∘ computeWApprox` (commitment recoverability) and runs the identification-scheme verifier;
this is precisely the equation `verify` checks, so an accepted forgery maps to a valid STMSIS
solution.

The `sampleParams` draws the same seed-based key as `keygen1`/`mldsaMLWE`: it samples `ρ` through
`ExpandSeed`, a uniform `t`, and publishes `(ExpandA(ρ), pk)` with `pk = ⟨ρ, Power2Round(t).1⟩`. -/
def mldsaSTMSIS (M : Type) :
    SelfTargetMSIS.Problem (TqMatrix p.k p.l) (Response p prims) (PublicKey p prims)
      (M × Commitment p prims) (CommitHashBytes p) where
  sampleParams := do
    let (pk, _) ← keygen1 p prims
    return (prims.expandA pk.rho, pk)
  isValid := fun aHat pk hashInput cTilde (z, h) =>
    -- Recover the commitment `w'` from `(pk, c̃, (z, h))`, bind it to the commitment component
    -- of the hashed preimage (the self-target binding), and run the identification verifier.
    let w' := prims.useHintVec h (computeWApprox p prims aHat (prims.sampleInBall cTilde) z pk.t1)
    decide (hashInput.2 = w') && (identificationScheme p prims).verify pk w' cTilde (z, h)

/-- **Self-target binding, made explicit.** An accepted `mldsaSTMSIS` solution is exactly the
identification-verifier acceptance *and* the binding of the recovered commitment `w'` to the
commitment component of the hashed preimage. Exposing the binding as its own conjunct keeps the
self-target requirement visible and hard to drop from the tailored relation: an instantiation that
silently ignored the preimage would fail this characterization. -/
theorem mldsaSTMSIS_isValid_eq_true_iff (aHat : TqMatrix p.k p.l) (pk : PublicKey p prims)
    (hashInput : M × Commitment p prims) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) (h : Vector prims.Hint p.k) :
    (mldsaSTMSIS p prims M).isValid aHat pk hashInput cTilde (z, h) = true ↔
      hashInput.2 = prims.useHintVec h
          (computeWApprox p prims aHat (prims.sampleInBall cTilde) z pk.t1) ∧
        (identificationScheme p prims).verify pk
          (prims.useHintVec h (computeWApprox p prims aHat (prims.sampleInBall cTilde) z pk.t1))
          cTilde (z, h) = true := by
  simp only [mldsaSTMSIS, Bool.and_eq_true, decide_eq_true_iff]

/-- **The SelfTargetMSIS extractor `C` (Lemma 7, Step 3).**

`C` runs the NMA forger `main` on the public key `pk` (the STMSIS target). The forger interacts with
the random oracle `H : (M × Commitment) →ₒ CommitHashBytes`. On a forgery `(msg, some (w', (z, h)))`
`C` outputs the STMSIS preimage `(msg, w')` together with the response `(z, h)`. An aborting forgery
`(msg, none)` is mapped to a dummy preimage with a zeroed response; the STMSIS experiment then reads
back `H(msg, default)`, which the forger may well have queried. That costs nothing: the NMA tail is
deterministically `false` on an abort, and the reduction's target is an upper bound on the NMA side,
so extra successes on the STMSIS side only add slack in the favorable direction. The matrix in
`params.1` is ignored by `C` (it equals `ExpandA(params.2.ρ)`).

The STMSIS experiment then looks up `c̃ = H(msg, w')` in the oracle cache and checks
`mldsaSTMSIS.isValid Â pk c̃ (z, h)`, which recomputes `w'` from `(pk, c̃, (z, h))` and runs the
identification verifier — exactly what the NMA `verify` does after querying `H(msg, w')`. -/
def extractorC [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    SelfTargetMSIS.Adversary (mldsaSTMSIS p prims M) where
  run := fun (params : TqMatrix p.k p.l × PublicKey p prims) => do
    let pk := params.2
    let (msg, σ) ← main pk
    match σ with
    | some (w', (z, h)) =>
      -- Force the RO answer `H(msg, w')` to be cached (the STMSIS experiment reads it back), then
      -- return the SelfTargetMSIS preimage/response.
      let _c ← HasQuery.query (spec := (M × Commitment p prims →ₒ CommitHashBytes p)) (msg, w')
      return ((msg, w'), (z, h))
    | none =>
      -- Aborting forgery: no valid preimage. Emit a dummy; the NMA tail is deterministically
      -- `false` here, so any STMSIS-side success on the dummy only loosens the bound favorably.
      return ((msg, default), default)

/-- **Per-key STMSIS read-back comparison.** For a fixed public key `pk`, the NMA forge-and-verify
tail (run through `simulateToProbComp`) accepts no more often than the SelfTargetMSIS experiment
tail of `extractorC` at the matching parameters `(ExpandA(ρ), pk)`.

Both tails first simulate `main pk` against the same random oracle from the empty cache; the proof
compares them after that shared prefix (`OracleComp.evalDist_bind_apply_mono_of_support`). On an
aborting forgery the NMA tail
is deterministically `false`. On a forgery `some (w', (z, h))` both branches issue the *same*
`H(msg, w')` query on the *same* cache, so the random answer `c̃` and the resulting cache coincide;
the STMSIS experiment then reads `c̃` back and `mldsaSTMSIS.isValid` recovers `w'` as exactly the
`useHintVec …` value that `verify` checks against, so an accepted NMA forgery is a valid STMSIS
solution. -/
private theorem stmsis_tail_le
    [DecidableEq M] [SampleableType (CommitHashBytes p)]
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims)))
    (pk : PublicKey p prims) :
    𝒟[simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← main pk
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ)]
        {true} ≤
      𝒟[do
        let ((hashInput, response), cache) ←
          (simulateQ (roImpl p prims (M := M))
            ((extractorC p prims main).run (prims.expandA pk.rho, pk))).run ∅
        match cache hashInput with
        | some hashOutput =>
            pure ((mldsaSTMSIS p prims M).isValid (prims.expandA pk.rho) pk hashInput hashOutput
              response)
        | none => pure false] {true} := by
  classical
  -- Decompose both tails over the shared simulation of `main pk` from the empty cache.
  unfold simulateToProbComp extractorC
  simp only [bind_pure_comp, simulateQ_bind, StateT.run_bind, StateT.run'_eq, map_bind,
    bind_assoc]
  -- Compare after the shared `main pk` simulation prefix.
  refine OracleComp.evalDist_bind_apply_mono_of_support (spec := unifSpec) _ _ _
    (measurableSet_singleton true) fun a _ => ?_
  -- `a = ((msg, σ), cache₀)`; split on whether the forgery aborts.
  obtain ⟨⟨msg, σ⟩, cache0⟩ := a
  cases σ with
  | none =>
    -- Aborting forgery: NMA `verify` is deterministically `false`, so the NMA tail has weight `0`.
    simp only [FiatShamirWithAbort, simulateQ_pure, StateT.run_pure, map_pure,
      evalDist_pure, Measure.dirac_apply]
    simp
  | some wzh =>
    obtain ⟨w', z, h⟩ := wzh
    -- Non-aborting forgery `(w', (z, h))`. Both branches issue the same `H(msg, w')` query on
    -- `cache0`; reduce the NMA `verify` and the extractor body to that single query.
    simp only [FiatShamirWithAbort, simulateQ_map, StateT.run_map, bind_pure_comp]
    -- Both sides are now `f <$> (simulateQ roImpl (query (msg, w'))).run cache0`; turn the maps
    -- into binds over the shared random-oracle run and compare per random answer `(c, cache₁)`.
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    refine OracleComp.evalDist_bind_apply_mono_of_support (spec := unifSpec) _ _ _
      (measurableSet_singleton true) fun cc hcc => ?_
    simp only [pure_bind]
    -- The query simulation caches its answer: `cc.2 (msg, w') = some cc.1`.
    have hquery : simulateQ (roImpl p prims (M := M)) (query (msg, w') :
          OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) _) =
        (randomOracle : QueryImpl (M × Commitment p prims →ₒ CommitHashBytes p) _) (msg, w') :=
      roSim.simulateQ_liftM_spec_query _ _
    rw [hquery] at hcc
    rw [randomOracle] at hcc
    rw [QueryImpl.withCaching_run_caches _ _ _ _ hcc]
    -- An accepted NMA forgery is a valid STMSIS solution. The self-target binding
    -- `hashInput.2 = w'` holds because the queried preimage is exactly `(msg, w')`, so the binding
    -- reduces to `decide (w' = w') = true`; commitment recoverability is the middle conjunct of
    -- `verify`, which `isValid` discharges by `decide (X = X)`.
    simp only [evalDist_pure, Measure.dirac_apply]
    by_cases hverify :
        (identificationScheme p prims).verify pk w' cc.1 (z, h) = true
    · -- Accepted: `isValid` recovers `w'` as the very `useHintVec …` value `verify` checks against,
      -- and the preimage's commitment component `(msg, w').2` is `w'`, so both conjuncts hold.
      have hvalid :
          (mldsaSTMSIS p prims M).isValid (prims.expandA pk.rho) pk (msg, w') cc.1 (z, h)
            = true := by
        simp only [mldsaSTMSIS, identificationScheme] at hverify ⊢
        revert hverify
        grind
      simp [hverify, hvalid]
    · simp only [Bool.not_eq_true] at hverify
      rw [hverify]
      simp

/-- **The SelfTargetMSIS extraction bound (Lemma 7, Step 3).** The uniform-`t` EUF-NMA advantage is
bounded by the SelfTargetMSIS advantage of the extractor `C`.

A forgery accepted by the NMA game (after the `H(msg, w')` query inside `verify`) is exactly a valid
SelfTargetMSIS solution for `mldsaSTMSIS`: `C` reproduces the forger's oracle trace, the
experiment's RO-consistency lookup recovers the same `c̃ = H(msg, w')`, `isValid` recovers `w'` and
runs the identical verifier. The reduction to the per-key comparison `stmsis_tail_le` is the
bundled-semantics rewrite (`nmaExperiment_eq_keygen_bind`) plus monotonicity over the shared
`keygen1` prefix; the per-key step then handles the cache read-back and commitment
recoverability. -/
theorem nmaAdvantage_keygen1_le_stmsis
    [DecidableEq M] [SampleableType (CommitHashBytes p)]
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    nmaAdvantage p prims hr maxAttempts (keygen1 p prims) main ≤
      SelfTargetMSIS.advantage (extractorC p prims main) := by
  -- Both acceptance probabilities reduce, through the shared `withStateOracle` random-oracle
  -- semantics, to:
  --   sample the uniform-`t` key `(pk, _)`; run `main pk` against the RO; on `some (w', (z,h))`
  --   read `c̃ = H(msg, w')` from the cache and accept iff `ids.verify pk w' c̃ (z,h)`.
  -- The NMA game performs exactly this (its `verify` queries `H(msg, w')` then runs `ids.verify`);
  -- the STMSIS experiment performs exactly this (its RO-consistency lookup yields `c̃`, and
  -- `mldsaSTMSIS.isValid` recovers `w'` from `(pk, c̃, (z,h))` and runs `ids.verify`).  After the
  -- bundled-semantics rewrite (`nmaExperiment_eq_keygen_bind`) both sides bind over the same
  -- `keygen1` prefix, so measure-bind monotonicity reduces to the per-key comparison
  -- `stmsis_tail_le`, which packages the cache read-back and commitment recoverability.
  classical
  rw [nmaAdvantage, nmaExperiment_eq_keygen_bind, SelfTargetMSIS.advantage,
    SelfTargetMSIS.experiment]
  -- The STMSIS `sampleParams` is exactly `keygen1` followed by publishing `(ExpandA(ρ), pk)`, so
  -- both event measures bind over the same `keygen1` prefix; compare them per-key.
  rw [show (mldsaSTMSIS p prims M).sampleParams =
      (keygen1 p prims) >>= fun pkSk => pure (prims.expandA pkSk.1.rho, pkSk.1) from rfl]
  rw [bind_assoc]
  refine OracleComp.evalDist_bind_apply_mono_of_support (spec := unifSpec) _ _ _
    (measurableSet_singleton true) ?_
  rintro ⟨pk, sk⟩ _
  rw [pure_bind]
  convert stmsis_tail_le p prims hr maxAttempts main pk using 2
  rw [roImpl, OracleSpec.romImpl, unifFwdImpl]
  apply congrArg (fun mx : ProbComp Bool => 𝒟[mx])
  refine bind_congr fun x => ?_
  obtain ⟨⟨hashInput, response⟩, cache⟩ := x
  dsimp only
  cases cache hashInput <;> rfl

/-! ### Tailored SelfTargetMSIS leg in the idealized short-key model

The declarations below add the short-model counterpart of the SelfTargetMSIS extraction:
the tailored problem `mldsaSTMSISShort` (self-target binding + the short-scheme verifier), its
algebraic characterization lemmas, the extractor `extractorCShort`, and the NMA-to-STMSIS
extraction bound `nmaAdvantage_keygenShort1_le_stmsis`. They reuse the shared extractor
`extractorC` and the seed-based helpers from the enclosing section. -/

/-- **The SelfTargetMSIS problem embedded by ML-DSA verification in the idealized short-key
model.** The validity predicate recovers the
commitment `w'` from `(pk, c̃, (z, h))` via `UseHint ∘ computeWApprox`, requires it to equal
the commitment component of the hash preimage (the self-target binding), and runs the
identification-scheme verifier (the short-scheme constant `identificationSchemeShort`),
and the parameters are sampled from the idealized
uniform-`t` key generator `keygenShort1`: the matrix seed `ρ`, the signing key `K`, and the
short secrets are drawn independently, `t` is uniform, and the published pair is
`(ExpandA(ρ), pk)` with `pk = ⟨ρ, Power2Round(t).1⟩`. This is the STMSIS instance matching the
exact short-model key-swap hop (`nma_keyswap_hop_short`).

Accepted solutions are characterized algebraically by `stmsisAlgebraicSolution` via the
bridge `mldsaSTMSISShort_isValid_iff`: the verifier's norm gates `‖z‖∞ < γ₁ − β` and
`weight(h) ≤ ω`, the hint-recovered matrix equation
`w' = UseHint(h, Â·z − SampleInBall(c̃)·(t₁·2^d))` over `R_q`, and the self-target binding
`hashInput.2 = w'` tying the recovered commitment to the pair hashed to produce `c̃`, whose
RO consistency is enforced by the surrounding `SelfTargetMSIS.experiment`. At the matched
parameters published by `sampleParams` acceptance is the norm gates plus the binding
(`mldsaSTMSISShort_isValid_expandA_iff`). The relation is the tailored verifier relation, not
the standard SelfTargetMSIS normal form `[I_m | A] · y` with the challenge in the final
coefficient block of `y`; reducing the tailored relation to that normal form is follow-up
work. -/
noncomputable def mldsaSTMSISShort (M : Type) :
    SelfTargetMSIS.Problem (TqMatrix p.k p.l) (Response p prims) (PublicKey p prims)
      (M × Commitment p prims) (CommitHashBytes p) where
  sampleParams := do
    let (pk, _) ← keygenShort1 p prims
    return (prims.expandA pk.rho, pk)
  isValid := fun aHat pk hashInput cTilde (z, h) =>
    -- Recover the commitment `w'` from `(pk, c̃, (z, h))`, bind it to the commitment component
    -- of the hashed preimage, and run the identification verifier.
    let w' := prims.useHintVec h (computeWApprox p prims aHat (prims.sampleInBall cTilde) z pk.t1)
    decide (hashInput.2 = w') && (identificationSchemeShort p prims).verify pk w' cTilde (z, h)

/-! ### Algebraic content of the tailored SelfTargetMSIS problem

`mldsaSTMSISShort.isValid` is defined through the identification-scheme verifier plus the
self-target binding. The declarations below re-express an accepted solution in explicit
algebraic form — the norm gates, the hint-recovered matrix equation over `R_q`, and the
binding of the recovered commitment to the hashed preimage. That algebraic form is the
endpoint reached here: it is the tailored verifier relation, and reducing it to the standard
SelfTargetMSIS normal form `[I_m | A] · y` (challenge in the final coefficient block of the
short preimage `y`) is follow-up work. -/

/-- **What the identification verifier's accept means algebraically.** With
`c = SampleInBall(c̃)`, the verifier accepts `(w₁, c̃, (z, h))` exactly when the norm gates
`‖z‖∞ < γ₁ − β` and `weight(h) ≤ ω` hold and the published commitment `w₁` satisfies the
self-target matrix equation `UseHint(h, ExpandA(ρ)·z − c·(t₁·2^d)) = w₁` over `R_q`. In the
Fiat-Shamir game `w₁` is the very commitment hashed to produce `c̃`, so an accepted NMA
forgery carries the tailored algebraic verifier relation, which is exactly the relation the
tailored problem `mldsaSTMSISShort` checks. Reducing that relation to the standard
SelfTargetMSIS normal form `[I_m | A] · y`, with the challenge in the final coefficient block
of the short preimage `y`, remains follow-up work.

Only the transform-isomorphism laws `NTTRingLaws` are consumed (via
`computeWApprox_eq_mul_sub_smul`), not the full `Primitives.Laws`. -/
theorem identificationSchemeShort_verify_eq_true_iff (h_transform : NTTRingLaws nttOps)
    (pk : PublicKey p prims) (w1 : Commitment p prims) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) (h : Vector prims.Hint p.k) :
    (identificationSchemeShort p prims).verify pk w1 cTilde (z, h) = true ↔
      polyVecNorm z < p.gamma1 - p.beta ∧
      prims.hintWeight h ≤ p.omega ∧
      prims.useHintVec h (prims.expandA pk.rho * z -
        prims.sampleInBall cTilde • prims.power2RoundShiftVec pk.t1) = w1 := by
  simp only [identificationSchemeShort, identificationScheme,
    computeWApprox_eq_mul_sub_smul p prims h_transform, Bool.and_eq_true,
    decide_eq_true_eq]
  tauto

/-- **The explicit algebraic SelfTargetMSIS relation extracted from `mldsaSTMSISShort`.**
Writing `c = SampleInBall(c̃)` and `t₁·2^d = power2RoundShiftVec t₁`, a solution `(z, h)`
for an instance matrix `Â` and target `pk = (ρ, t₁)` consists of:

1. the verifier's **norm gates**, verbatim: `‖z‖∞ < γ₁ − β` and `weight(h) ≤ ω`;
2. the **matrix equation**: a commitment `w'` recovered from the hint,
   `w' = UseHint(h, Â·z − c·(t₁·2^d))` over `R_q` (the coefficient-domain reading of
   `computeWApprox`, see `computeWApprox_eq_mul_sub_smul`), which the verifier's own
   recomputation from the published seed reproduces:
   `UseHint(h, ExpandA(ρ)·z − c·(t₁·2^d)) = w'`;
3. the **self-target binding**: the commitment component of the hash preimage equals the
   recovered commitment, `hashInput.2 = w'` — the solution is bound to the very pair hashed
   to produce `c̃`.

The **RO-consistency** of `c̃` is deliberately not part of the relation: it is enforced by
the surrounding `SelfTargetMSIS.experiment` (cache read-back), not by `isValid`. The
relation quantifies nothing `isValid` does not check — it is a re-expression of
`mldsaSTMSISShort.isValid` (`mldsaSTMSISShort_isValid_iff`), not a strengthening; on the
matched parameters `Â = ExpandA(ρ)` published by `sampleParams` the two sides of the
recovered-commitment equation coincide and acceptance is the norm gates plus the binding
(`mldsaSTMSISShort_isValid_expandA_iff`). -/
def stmsisAlgebraicSolution (aHat : TqMatrix p.k p.l) (pk : PublicKey p prims)
    (hashInput : M × Commitment p prims) (cTilde : CommitHashBytes p) :
    Response p prims → Prop
  | (z, h) =>
    polyVecNorm z < p.gamma1 - p.beta ∧
    prims.hintWeight h ≤ p.omega ∧
    ∃ w' : Commitment p prims,
      w' = prims.useHintVec h
        (aHat * z - prims.sampleInBall cTilde • prims.power2RoundShiftVec pk.t1) ∧
      prims.useHintVec h (prims.expandA pk.rho * z -
        prims.sampleInBall cTilde • prims.power2RoundShiftVec pk.t1) = w' ∧
      hashInput.2 = w'

/-- **The algebraic bridge for the tailored SelfTargetMSIS problem.** An accepted
`mldsaSTMSISShort` solution is exactly an `stmsisAlgebraicSolution`: the verifier's norm
gates, the hint-recovered matrix equation over `R_q` with the recovered commitment `w'`
exhibited explicitly, and the self-target binding of `w'` to the commitment component of
the hashed preimage. Only the transform-isomorphism laws `NTTRingLaws` are consumed (via
`computeWApprox_eq_mul_sub_smul`), not the full `Primitives.Laws`. The characterization is
of the tailored relation; the standard SelfTargetMSIS normal form `[I_m | A] · y` is not
reached here. -/
theorem mldsaSTMSISShort_isValid_iff (h_transform : NTTRingLaws nttOps)
    (aHat : TqMatrix p.k p.l) (pk : PublicKey p prims) (hashInput : M × Commitment p prims)
    (cTilde : CommitHashBytes p) (z : RqVec p.l) (h : Vector prims.Hint p.k) :
    (mldsaSTMSISShort p prims M).isValid aHat pk hashInput cTilde (z, h) = true ↔
      stmsisAlgebraicSolution p prims aHat pk hashInput cTilde (z, h) := by
  simp only [mldsaSTMSISShort, identificationSchemeShort, identificationScheme,
    stmsisAlgebraicSolution, computeWApprox_eq_mul_sub_smul p prims h_transform,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hbind, ⟨hz, hw⟩, hweight⟩
    exact ⟨hz, hweight, _, rfl, hw, hbind⟩
  · rintro ⟨hz, hweight, w', rfl, hw, hbind⟩
    exact ⟨hbind, ⟨hz, hw⟩, hweight⟩

/-- **Characterization at the matched parameters.** `mldsaSTMSISShort.sampleParams` always
publishes the matrix as `Â = ExpandA(pk.ρ)`, and at such matched parameters the verifier's
own recomputation from the published seed coincides with the recovered commitment, so
acceptance is exactly the two norm gates plus the **self-target binding**: the commitment
component of the hashed preimage must equal the commitment
`UseHint(h, Â·z − SampleInBall(c̃)·(t₁·2^d))` recomputed from the response (stated through
`computeWApprox`; see `computeWApprox_eq_mul_sub_smul` for the coefficient-domain reading).
In particular the trivial response `z = 0` with a weight-`0` hint wins only when the
adversary has hashed the exact commitment `UseHint(0, −SampleInBall(c̃)·(t₁·2^d))` — a value
determined by the challenge `c̃` that the random oracle returns only *after* the preimage is
fixed. No primitive laws are needed. -/
theorem mldsaSTMSISShort_isValid_expandA_iff (pk : PublicKey p prims)
    (hashInput : M × Commitment p prims) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) (h : Vector prims.Hint p.k) :
    (mldsaSTMSISShort p prims M).isValid (prims.expandA pk.rho) pk hashInput cTilde
        (z, h) = true ↔
      polyVecNorm z < p.gamma1 - p.beta ∧ prims.hintWeight h ≤ p.omega ∧
      hashInput.2 = prims.useHintVec h (computeWApprox p prims (prims.expandA pk.rho)
        (prims.sampleInBall cTilde) z pk.t1) := by
  simp only [mldsaSTMSISShort, identificationSchemeShort, identificationScheme,
    Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- **The SelfTargetMSIS extractor for the idealized short-key model.** It performs the same
forger-to-preimage extraction as `extractorC` — run the NMA forger `main` on the target public
key, force the `H(msg, w')` query, and output the STMSIS preimage `(msg, w')` with the response
`(z, h)` — typed against the short-model problem `mldsaSTMSISShort`, whose parameters are sampled
from `keygenShort1`. -/
noncomputable def extractorCShort [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    SelfTargetMSIS.Adversary (mldsaSTMSISShort p prims M) :=
  ⟨(extractorC p prims main).run⟩

/-! ### The verifier at an explicit matrix and the shared extraction tail

The identification verifier evaluates `ExpandA` once, at the public seed. Abstracting that
evaluation into a parameter gives `verifyWithMatrix`, and the Fiat-Shamir verification over it
`verifyAtMatrix`. The per-key extraction comparison `stmsis_tail_le_withMatrix` is stated at an
explicit matrix, so it serves both the short model here (at `ExpandA(pk.ρ)`) and the `ExpandA`
random-oracle model of `LatticeCrypto.MLDSA.SecurityExpandARO` (at the programmed matrix). -/

/-- The ML-DSA identification verifier at an explicitly supplied public matrix `aHat`
(FIPS 204 Algorithm 8, lines 8–13): check `‖z‖∞ < γ₁ − β`, recover
`w'_Approx = Â·z − c·(t₁·2^d)` from `aHat`, and require `UseHint(h, w'_Approx) = w₁` and hint
weight `≤ ω`. `identificationScheme.verify` is this verifier at `aHat := ExpandA(pk.ρ)`
(`identificationScheme_verify_eq_verifyWithMatrix`); the `ExpandA` random-oracle verifier
`NMA.verifyRO` supplies `aHat` by an oracle query instead. -/
def verifyWithMatrix (aHat : TqMatrix p.k p.l) (pk : PublicKey p prims)
    (w1 : Commitment p prims) (cTilde : CommitHashBytes p) : Response p prims → Bool
  | (z, h) =>
    let c := prims.sampleInBall cTilde
    let wApprox := computeWApprox p prims aHat c z pk.t1
    let w1' := prims.useHintVec h wApprox
    decide (polyVecNorm z < p.gamma1 - p.beta) &&
    decide (w1' = w1) &&
    decide (prims.hintWeight h ≤ p.omega)

/-- The identification verifier evaluates `ExpandA` exactly once, at the public seed: it is
`verifyWithMatrix` at `ExpandA(pk.ρ)`. -/
theorem identificationScheme_verify_eq_verifyWithMatrix (pk : PublicKey p prims)
    (w1 : Commitment p prims) (cTilde : CommitHashBytes p) (zh : Response p prims) :
    (identificationScheme p prims).verify pk w1 cTilde zh =
      verifyWithMatrix p prims (prims.expandA pk.rho) pk w1 cTilde zh := by
  rcases zh with ⟨z, h⟩
  rfl

/-- The short-tagged scheme carries the same verifier (`identificationSchemeShort` re-uses the
operations of `identificationScheme`), so it too is `verifyWithMatrix` at `ExpandA(pk.ρ)`. -/
theorem identificationSchemeShort_verify_eq_verifyWithMatrix (pk : PublicKey p prims)
    (w1 : Commitment p prims) (cTilde : CommitHashBytes p) (zh : Response p prims) :
    (identificationSchemeShort p prims).verify pk w1 cTilde zh =
      verifyWithMatrix p prims (prims.expandA pk.rho) pk w1 cTilde zh :=
  identificationScheme_verify_eq_verifyWithMatrix p prims pk w1 cTilde zh

/-- Fiat-Shamir-with-aborts verification at an explicit matrix `aHat`, in the two-oracle world of
the signature: an absent signature is rejected; on `some (w', z)` the challenge is queried from
`H` and `verifyWithMatrix` decides. At `aHat := ExpandA(pk.ρ)` this is the signature's own
`verify` (`verifyAtMatrix_expandA`); the random-oracle reductions use it at the matrix they
programmed. -/
def verifyAtMatrix (aHat : TqMatrix p.k p.l) (pk : PublicKey p prims) (msg : M)
    (σ : Option (Commitment p prims × Response p prims)) :
    OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) Bool :=
  match σ with
  | none => pure false
  | some (w', z) => do
    let c ← HasQuery.query (spec := (M × Commitment p prims →ₒ CommitHashBytes p)) (msg, w')
    pure (verifyWithMatrix p prims aHat pk w' c z)

/-- At the honest matrix `ExpandA(pk.ρ)`, `verifyAtMatrix` is the verification algorithm of the
short-model ML-DSA signature `FiatShamirWithAbort (identificationSchemeShort …)`. -/
theorem verifyAtMatrix_expandA
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ) (pk : PublicKey p prims) (msg : M)
    (σ : Option (Commitment p prims × Response p prims)) :
    verifyAtMatrix p prims (prims.expandA pk.rho) pk msg σ =
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)))
        (identificationSchemeShort p prims) hr M maxAttempts).verify pk msg σ := by
  rcases σ with _ | ⟨w', z, h⟩ <;> rfl

/-- The tailored SelfTargetMSIS validity predicate at an explicit matrix `aHat`: recover
`w' = UseHint(h, Â·z − SampleInBall(c̃)·(t₁·2^d))` from `aHat`, bind it to the commitment
component of the hashed preimage (the self-target binding), and run `verifyWithMatrix` at `aHat`.
At `aHat = ExpandA(pk.ρ)` it is the validity predicate of `mldsaSTMSISShort`
(`mldsaSTMSISShort_isValid_expandA_eq_withMatrix`). -/
def stmsisValidWithMatrix (aHat : TqMatrix p.k p.l) (pk : PublicKey p prims)
    (hashInput : M × Commitment p prims) (cTilde : CommitHashBytes p) :
    Response p prims → Bool
  | (z, h) =>
    let w' := prims.useHintVec h (computeWApprox p prims aHat (prims.sampleInBall cTilde) z pk.t1)
    decide (hashInput.2 = w') && verifyWithMatrix p prims aHat pk w' cTilde (z, h)

/-- At the honest matrix `ExpandA(pk.ρ)`, the short-model tailored problem accepts exactly the
solutions that `stmsisValidWithMatrix` accepts. -/
theorem mldsaSTMSISShort_isValid_expandA_eq_withMatrix (pk : PublicKey p prims)
    (hashInput : M × Commitment p prims) (cTilde : CommitHashBytes p) (zh : Response p prims) :
    (mldsaSTMSISShort p prims M).isValid (prims.expandA pk.rho) pk hashInput cTilde zh =
      stmsisValidWithMatrix p prims (prims.expandA pk.rho) pk hashInput cTilde zh := by
  rcases zh with ⟨z, h⟩
  rfl

/-- **Per-key STMSIS read-back comparison at an explicit matrix.** For a fixed public key `pk`
and matrix `aHat`, the forge-and-verify tail at `aHat` (run through `simulateToProbComp`) accepts
no more often than the SelfTargetMSIS experiment tail of `extractorC` at the parameters
`(aHat, pk)` with `stmsisValidWithMatrix` validity. The argument never inspects the key
distribution: both tails simulate `main pk` against the same random oracle from the empty cache,
an aborting forgery contributes weight `0`, and on `some (w', (z, h))` both branches issue the
same `H(msg, w')` query, whose cached answer the STMSIS experiment reads back before the
validity predicate recovers the commitment, binds it to the preimage component `w'`, and runs
the identical verifier at `aHat`. -/
theorem stmsis_tail_le_withMatrix
    [DecidableEq M] [SampleableType (CommitHashBytes p)]
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (aHat : TqMatrix p.k p.l)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims)))
    (pk : PublicKey p prims) :
    𝒟[simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← main pk
        verifyAtMatrix p prims aHat pk msg σ)] {true} ≤
      𝒟[do
        let ((hashInput, response), cache) ←
          (simulateQ (roImpl p prims (M := M))
            ((extractorC p prims main).run (aHat, pk))).run ∅
        match cache hashInput with
        | some hashOutput =>
            pure (stmsisValidWithMatrix p prims aHat pk hashInput hashOutput response)
        | none => pure false] {true} := by
  classical
  -- Decompose both tails over the shared simulation of `main pk` from the empty cache.
  unfold simulateToProbComp extractorC
  simp only [bind_pure_comp, simulateQ_bind, StateT.run_bind, StateT.run'_eq, map_bind,
    bind_assoc]
  refine OracleComp.evalDist_bind_apply_mono_of_support (spec := unifSpec) _ _ _
    (measurableSet_singleton true) fun a _ => ?_
  obtain ⟨⟨msg, σ⟩, cache0⟩ := a
  cases σ with
  | none =>
    -- Aborting forgery: the verify tail is deterministically `false`, so it has weight `0`.
    simp only [verifyAtMatrix, simulateQ_pure, StateT.run_pure, map_pure, evalDist_pure,
      Measure.dirac_apply]
    simp
  | some wzh =>
    obtain ⟨w', z, h⟩ := wzh
    -- Both branches issue the same `H(msg, w')` query on `cache0`; compare per random answer.
    simp only [verifyAtMatrix, simulateQ_map, StateT.run_map, bind_pure_comp]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    refine OracleComp.evalDist_bind_apply_mono_of_support (spec := unifSpec) _ _ _
      (measurableSet_singleton true) fun cc hcc => ?_
    simp only [pure_bind]
    -- The query simulation caches its answer: `cc.2 (msg, w') = some cc.1`.
    have hquery : simulateQ (roImpl p prims (M := M)) (query (msg, w') :
          OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) _) =
        (randomOracle : QueryImpl (M × Commitment p prims →ₒ CommitHashBytes p) _) (msg, w') :=
      roSim.simulateQ_liftM_spec_query _ _
    rw [hquery] at hcc
    rw [randomOracle] at hcc
    rw [QueryImpl.withCaching_run_caches _ _ _ _ hcc]
    -- An accepted forgery is a valid solution: the verifier's middle conjunct identifies the
    -- recomputed commitment with `w'`, which is the commitment component of the preimage.
    simp only [evalDist_pure, Measure.dirac_apply]
    by_cases hverify : verifyWithMatrix p prims aHat pk w' cc.1 (z, h) = true
    · have hvalid :
          stmsisValidWithMatrix p prims aHat pk (msg, w') cc.1 (z, h) = true := by
        simp only [stmsisValidWithMatrix, verifyWithMatrix] at hverify ⊢
        revert hverify
        grind
      simp [hverify, hvalid]
    · simp only [Bool.not_eq_true] at hverify
      rw [hverify]
      simp

/-- **Per-key STMSIS read-back comparison, short model.** `stmsis_tail_le_withMatrix` at the
honest matrix `ExpandA(pk.ρ)`, where `verifyAtMatrix` is the short scheme's verification
(`verifyAtMatrix_expandA`), `extractorCShort` runs `extractorC`, and the validity predicate is
that of `mldsaSTMSISShort` (`mldsaSTMSISShort_isValid_expandA_eq_withMatrix`); all three
identifications are definitional. -/
private theorem stmsis_tail_le_short
    [DecidableEq M] [SampleableType (CommitHashBytes p)]
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims)))
    (pk : PublicKey p prims) :
    𝒟[simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← main pk
        (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify
          pk msg σ)] {true} ≤
      𝒟[do
        let ((hashInput, response), cache) ←
          (simulateQ (roImpl p prims (M := M))
            ((extractorCShort p prims main).run (prims.expandA pk.rho, pk))).run ∅
        match cache hashInput with
        | some hashOutput =>
            pure ((mldsaSTMSISShort p prims M).isValid (prims.expandA pk.rho) pk
              hashInput hashOutput response)
        | none => pure false] {true} := by
  exact stmsis_tail_le_withMatrix p prims (prims.expandA pk.rho) main pk

/-- **The SelfTargetMSIS extraction bound in the idealized short-key model.** The uniform-`t`
short-model EUF-NMA advantage (key generator `keygenShort1`) is bounded by the SelfTargetMSIS
advantage of the extractor against `mldsaSTMSISShort`.

The argument is a shared-prefix read-back comparison: after the
bundled-semantics rewrite (`nmaShortExperiment_eq_keygen_bind`) both sides bind over the same
`keygenShort1` prefix — the short problem's `sampleParams` is definitionally `keygenShort1`
followed by publishing `(ExpandA(ρ), pk)` — so monotonicity reduces to the per-key comparison
`stmsis_tail_le_short`, which never inspects the key distribution and packages the cache
read-back and commitment recoverability. -/
theorem nmaAdvantage_keygenShort1_le_stmsis
    [DecidableEq M] [SampleableType (CommitHashBytes p)]
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    nmaShortAdvantage p prims hr maxAttempts (keygenShort1 p prims) main ≤
      SelfTargetMSIS.advantage (extractorCShort p prims main) := by
  classical
  rw [nmaShortAdvantage, nmaShortExperiment_eq_keygen_bind, SelfTargetMSIS.advantage,
    SelfTargetMSIS.experiment]
  -- The short STMSIS `sampleParams` is exactly `keygenShort1` followed by publishing
  -- `(ExpandA(ρ), pk)`, so both event measures bind over the same prefix; compare them per-key.
  rw [show (mldsaSTMSISShort p prims M).sampleParams =
      (keygenShort1 p prims) >>= fun pkSk => pure (prims.expandA pkSk.1.rho, pkSk.1) from rfl]
  rw [bind_assoc]
  refine OracleComp.evalDist_bind_apply_mono_of_support (spec := unifSpec) _ _ _
    (measurableSet_singleton true) ?_
  rintro ⟨pk, sk⟩ _
  rw [pure_bind]
  convert stmsis_tail_le_short p prims hr maxAttempts main pk using 2
  rw [roImpl, OracleSpec.romImpl, unifFwdImpl]
  apply congrArg (fun mx : ProbComp Bool => 𝒟[mx])
  refine bind_congr fun x => ?_
  obtain ⟨⟨hashInput, response⟩, cache⟩ := x
  dsimp only
  cases cache hashInput <;> rfl

end Extractor

end NMA

/-! ## Status

The live short-secret reduction and the extraction bound are fully proven:

- **MLWE key swap (`nma_keyswap_hop_short`).** The exact NMA-game gap for
  `keygenShort` / `keygenShort1` is the advantage of `distinguisherBShort` against
  `mldsaMLWEShort`. The uniform-matrix statement is `MLDSA.NMA.nma_security_rom` in
  `LatticeCrypto.MLDSA.SecurityExpandARO`, which models `ExpandA` as a random oracle. The older
  `mldsaMLWE` / `distinguisherB` declarations are scaffolding only: their full-ring real branch
  is not the seed-derived `keygen0` distribution.
- **STMSIS extraction (`nmaAdvantage_keygen1_le_stmsis`).** The uniform-`t` NMA advantage is bounded
  by the SelfTargetMSIS advantage of `extractorC`; after `nmaExperiment_eq_keygen_bind` both sides
  bind over the same `keygen1` prefix, so `OracleComp.evalDist_bind_apply_mono_of_support` reduces
  to the per-key lemma
  `stmsis_tail_le`, which couples the single `H(msg, w')` query (the cached answer is read back and
  `verify = true → isValid = true` closes the per-answer inequality).
-/

end MLDSA
