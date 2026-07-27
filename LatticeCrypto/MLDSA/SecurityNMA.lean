/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import LatticeCrypto.MLDSA.Security
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# ML-DSA EUF-NMA Security: the short-key MLWE reduction (Lemma 7)

This file builds the reduction infrastructure for the ML-DSA EUF-NMA security theorem
`MLDSA.nma_security_short` (the Dilithium Lemma 7) over the idealized short-secret key
generation `keygenShort`, together with its transfer to the FIPS seed-derived key
generation `keygen0`:

1. **MLWE key-swap (`nma_keyswap_hop_short`).** Replace the honest short-key generation,
   where the public key vector is `t = Â · s₁ + s₂` with `(s₁, s₂)` uniform on the
   `η`-bounded box, by the variant `keygenShort1` that samples `t` uniformly. The gap
   between the two EUF-NMA games **is** the decisional `mldsaMLWEShort` advantage of the
   induced distinguisher `distinguisherBShort`: both branch identifications are exact monad
   identities, so no statistical slack appears.
2. **SelfTargetMSIS extraction (`nmaAdvantage_keygenShort1_le_stmsis`).** Once `t` is uniform
   the key carries no secret, so a forgery is a short vector satisfying the SelfTargetMSIS
   relation; the extractor `extractorCShort` reads `(z, c̃)` out of the forged signature. The
   shared random-oracle simulation lines up the NMA `verify` query with the extractor's RO
   read-back (`stmsis_tail_le_short`), and an accepted forgery is a valid SelfTargetMSIS
   solution by commitment recoverability.
3. **FIPS transfer (`nma_security_fips`).** The deterministic seed-expanded FIPS key generator
   `keygen0` is related to `keygenShort` by the named XOF-replacement assumption
   `expandSReplacement`, so the short-model bound transfers to the FIPS key generation at an
   additive `εPRG`.

The `H₁` reprogramming step of the paper folds into the random-oracle modeling and is not
separated out here. `MLDSA.nma_security_short` assembles steps 1 and 2 under the bridge
hypotheses negotiated in its statement (`hGen`, `hStmsis`, `hMlweBridge`).

## Why the secrets are short

In a finite additive group, adding an independent full-carrier-uniform error makes the sum
uniform whatever the secret is, so an MLWE problem whose `sampleError` is uniform on all of
`RqVec p.k` has real and uniform branches that coincide and advantage identically zero. The
hardness of ML-DSA key generation lives entirely in the *shortness* of `(s₁, s₂)`: both the
secret and the error are drawn by `sampleShortVec` from the `η`-bounded box `S_η`, which is
the distribution the ML-DSA Module-LWE assumption is stated over, and `Â · s₁ + s₂` with
short `(s₁, s₂)` is far from uniform. For the same reason the FIPS-to-ideal step compares
`ExpandS` against *short* independent sampling (`expandSReplacement`), never against
full-ring uniformity: a random-oracle treatment of a XOF can justify replacing its output by
independent draws with the same marginals, and the FIPS marginals of `ExpandS` are short.

## Scope: an idealized proof-level ML-DSA model

The theorems here are about the **proof-level** scheme
`FiatShamirWithAbort (identificationSchemeShort p prims)`, not the FIPS 204 signing/encoding
path. The idealizations, explicitly:

- Signatures are the identification-scheme transcripts `(commitment, challenge hash,
  response)`; the FIPS byte-level encodings, hints, and the `Signature.lean` packing layer are
  not part of the statement.
- The headline key generation is the idealized `keygenShort` — `ρ`, `K` uniform and `(s₁, s₂)`
  uniform on the `η`-bounded box. The deterministic FIPS derivation `keygen0` is covered by
  the corollary `nma_security_fips` under the explicit computational assumption
  `expandSReplacement`.
- The hardness problems are stated over the seed-based key embedding (`mldsaMLWEShort`,
  `mldsaSTMSISShort`); bridging to the standard matrix-based MLWE problem is carried by the
  `hMlweBridge` hypothesis, with the canonical discharge landing on `mldsaMatrixMLWE` via
  `advantage_mldsaMLWEShort_le_matrix` under `expandAIdealization`.
- No cost model is attached: the reductions are constructed explicitly but their polynomial
  runtime is not machine-checked.

## What is defined here

The idealized ML-DSA key distribution embeds an MLWE instance: sample a public seed `ρ` and a
signing key `K`, set the public matrix `Â = ExpandA(ρ)`, sample short secrets `(s₁, s₂)`
uniformly on the `η`-bounded box, and publish the `Power2Round` high half of
`t = Â · s₁ + s₂`. The uniform-`t` variant replaces `Â · s₁ + s₂` by a uniform sample. We
package both as `ProbComp` key generators, lift each to an EUF-NMA game over an arbitrary
forging adversary `main`, and exhibit the MLWE distinguisher that interpolates between them:
it reconstructs the public key from the challenge `(ρ, t)` and runs the adversary.

## Modeling note (seeds, not matrices)

The verifier recomputes `Â = ExpandA(pk.ρ)` from the seed stored in the public key, so the
MLWE challenge matrix `Â` must be presented to the adversary *through* a seed `ρ`. Rather than
carrying an embedding witness `ExpandA(ρ) = Â` (which need not exist, since `ExpandA` is not
surjective), we **seed-base** the MLWE problem: the public challenge of `mldsaMLWEShort` is the
*seed* `ρ` itself, and the matrix is *defined* as `Â := ExpandA(ρ)` wherever it is used, so
that `noiseless s₁ ρ = ExpandA(ρ)·s₁`. This is the standard ROM modeling of Dilithium with
`ExpandA` a random oracle, and it makes the distinguisher total: it consumes `(ρ, t)` and forms
`pk = (ρ, Power2Round(t).1)` directly with no embedding. The seed-based problem reduces to the
standard uniform-matrix `mldsaMatrixMLWE` under the explicit `expandAIdealization` assumption
(`advantage_mldsaMLWEShort_le_matrix`).
-/

open OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

namespace NMA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]

section KeyGen

variable [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]

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

/-- **FIPS key generation.** Sample a seed, expand it into `(ρ, ρ', key)` and the secrets
`(s₁, s₂)`, then form the key from `t = ExpandA(ρ) · s₁ + s₂`. This is `keyGenFromSeed`
phrased as a `ProbComp` over the uniform seed distribution. -/
def keygen0 : ProbComp (PublicKey p prims × SecretKey p) := do
  let seed ← $ᵗ (Bytes 32)
  let (rho, rhoPrime, key) := prims.expandSeed seed
  let (s1, s2) := prims.expandS rhoPrime
  let t := prims.expandA rho * s1 + s2
  return keyFromMaterial p prims rho key s1 s2 t

omit [DecidableEq prims.High] [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] in
/-- `keyFromMaterial` reproduces `keyGenFromSeed` on the honest material derived from a seed. -/
theorem keyFromMaterial_eq (seed : Bytes 32) :
    let (rho, rhoPrime, key) := prims.expandSeed seed
    let (s1, s2) := prims.expandS rhoPrime
    keyFromMaterial p prims rho key s1 s2 (prims.expandA rho * s1 + s2) =
      keyGenFromSeed p prims seed := by
  simp only [keyFromMaterial, keyGenFromSeed]

/-! ### Short-secret sampling and the idealized key generators

The FIPS key generator derives everything deterministically from one seed (`keygen0` above).
The idealized proof-level model instead samples the matrix seed `ρ`, the signing key `K`, and
the short secrets `(s₁, s₂)` independently, with `(s₁, s₂)` uniform on the `η`-bounded box
`S_η^ℓ × S_η^k` — the distribution the Module-LWE assumption for ML-DSA is stated over. The
key-swap hop is then an exact monad identity against `mldsaMLWEShort` (no statistical slack),
and the deterministic-XOF derivation enters only through the separate `expandSReplacement`
assumption consumed by the FIPS-keygen corollary. -/

/-- `polyVecBounded` is a decidable predicate: it is a `≤` test on the computed
centered infinity norm. -/
instance {k b : ℕ} : DecidablePred (fun v : RqVec k => polyVecBounded v b) := fun _ => by
  unfold polyVecBounded
  exact Nat.decLe _ _

omit nttOps in
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
    simp only [LatticeCrypto.zmodCenteredCoeffView, LatticeCrypto.centeredRepr, ZMod.val_zero,
      Int.natCast_zero]
    split <;> omega
  calc normOps.cInfNorm (0 : Rq) = polyNorm (0 : Rq) := rfl
    _ = 0 := h0
    _ ≤ b := Nat.zero_le b

/-- **Uniform sampling from the `η`-bounded box.** The uniform distribution on
`S_b^k = { v : RqVec k | ‖v‖∞ ≤ b }`, i.e. every coefficient of every component uniform on the
centered interval `[-b, b]`. This is the secret/error distribution of the Module-LWE assumption
used by ML-DSA (`η ∈ {2, 4}` for the approved parameter sets). -/
noncomputable def sampleShortVec (k b : ℕ) [SampleableType (RqVec k)] : ProbComp (RqVec k) :=
  letI : Fintype {v : RqVec k // polyVecBounded v b} := .ofFinite _
  letI : Nonempty {v : RqVec k // polyVecBounded v b} := ⟨0, polyVecBounded_zero k b⟩
  letI : SampleableType {v : RqVec k // polyVecBounded v b} := .ofFintype _
  Subtype.val <$> ($ᵗ {v : RqVec k // polyVecBounded v b})

/-- **Idealized key generation (real `t`).** Sample the matrix seed `ρ`, the signing key `K`,
and the short secrets `(s₁, s₂)` independently — `(s₁, s₂)` uniform on the `η`-bounded box —
and form `t = ExpandA(ρ) · s₁ + s₂`. This is the honestly-sampled key distribution of the
idealized proof-level ML-DSA model; the deterministic seed-expanded `keygen0` is related to it
by the `expandSReplacement` assumption. -/
noncomputable def keygenShort : ProbComp (PublicKey p prims × SecretKey p) := do
  let key ← $ᵗ (Bytes 32)
  let rho ← $ᵗ (Bytes 32)
  let s1 ← sampleShortVec p.l p.eta
  let s2 ← sampleShortVec p.k p.eta
  let t := prims.expandA rho * s1 + s2
  return keyFromMaterial p prims rho key s1 s2 t

/-- **Idealized key generation (uniform `t`).** Identical to `keygenShort` except the public
vector `t` is sampled uniformly. The gap between the two is exactly the `mldsaMLWEShort`
distinguishing advantage of the induced distinguisher (`nma_keyswap_hop_short`). -/
noncomputable def keygenShort1 : ProbComp (PublicKey p prims × SecretKey p) := do
  let key ← $ᵗ (Bytes 32)
  let rho ← $ᵗ (Bytes 32)
  let s1 ← sampleShortVec p.l p.eta
  let s2 ← sampleShortVec p.k p.eta
  let t ← $ᵗ (RqVec p.k)
  return keyFromMaterial p prims rho key s1 s2 t

omit nttOps in
/-- Every output of `sampleShortVec k b` lies in the `b`-bounded box: the sampler draws from
the subtype `{v // polyVecBounded v b}` and projects out the value, so support membership
carries the bound. -/
lemma mem_support_sampleShortVec {k b : ℕ} [SampleableType (RqVec k)] {v : RqVec k}
    (hv : v ∈ support (sampleShortVec k b)) : polyVecBounded v b := by
  simp only [sampleShortVec, support_map] at hv
  obtain ⟨u, -, rfl⟩ := hv
  exact u.property

/-- The generable relation carried by the idealized short-key model: the generator is
`keygenShort`, and every generated pair is material-valid. Each pair drawn by `keygenShort` is
literally `keyFromMaterial ρ K s₁ s₂ (ExpandA(ρ)·s₁ + s₂)` for uniform `ρ`, `K` and box-sampled
`(s₁, s₂)`, and `sampleShortVec` outputs are `η`-bounded on their support
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

omit [DecidableEq prims.High] in
/-- **Satisfiability certificate for the short-model `hGen` hypothesis.** Some generable
relation over `validKeyPairShort` has `keygenShort` as its generator — witnessed by `hrShort`.
The short-model security statements hypothesize such a relation via
`hGen : hr.gen = keygenShort p prims`; this theorem records that the hypothesis pair
`(hr, hGen)` is inhabited, so those statements have non-vacuous instances. -/
theorem keygenShort_generable :
    ∃ hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims),
      hr.gen = keygenShort p prims :=
  ⟨hrShort p prims, rfl⟩

/-- The generable relation carried by the FIPS seed-derived key generation: the generator is
`keygen0`, and every generated pair is seed-valid. Each pair drawn by `keygen0` is literally
the key assembled by `keyFromMaterial` from the material expanded out of its seed, which
`keyFromMaterial_eq` identifies with `keyGenFromSeed` — exactly the witness `validKeyPair` asks
for. This inhabits the `hGen` hypothesis of the FIPS-keygen security corollary
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

omit [DecidableEq prims.High] [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] in
/-- **Satisfiability certificate for the FIPS-keygen `hGen` hypothesis.** Some generable
relation over `validKeyPair` has the seed-derived FIPS key generator `keygen0` as its
generator — witnessed by `hrFips`. The FIPS-keygen security corollary hypothesizes such a
relation via `hGen : hr.gen = keygen0 p prims`; this theorem records that the hypothesis pair
`(hr, hGen)` is inhabited, so that statement has non-vacuous instances. -/
theorem keygen0_generable :
    ∃ hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims),
      hr.gen = keygen0 p prims :=
  ⟨hrFips p prims, rfl⟩

/-- **XOF replacement for the ML-DSA secret derivation (`ExpandSeed`/`ExpandS`), quantified
form.** For a real bound `εPRG`, this asserts that no distinguisher receiving `(ρ, K, s₁, s₂)`
can tell the FIPS derivation — expand a uniform 32-byte seed into `(ρ, ρ', K)` and derive
`(s₁, s₂) = ExpandS(ρ')` — from independent sampling with the correct short marginals: `ρ`, `K`
uniform and `(s₁, s₂)` uniform on the `η`-bounded box `S_η^ℓ × S_η^k`, i.e. exactly the draws of
the idealized key generator `keygenShort`.

This is the standard PRG/XOF-replacement reading of `ExpandSeed`/`ExpandS` against the
short-secret marginal: the ideal branch is the box distribution the Module-LWE assumption for
ML-DSA is stated over, so the assumption carries exactly the "SHAKE output is pseudorandom with
the FIPS marginals" step and nothing else. For a fixed deterministic `prims` the
unrestricted-quantifier form is only satisfiable at large `εPRG` — an unbounded distinguisher
can test membership in the `2^256`-point image of the seed expansion — so, pending a cost model
for the reductions, it should be read computationally, against bounded distinguishers, where it
is the assumption that the SHAKE-derived `(ρ, K, s₁, s₂)` is pseudorandom with the FIPS
marginals. It is consumed by the FIPS-keygen corollary `nma_security_fips` to transfer the
short-model bound to `keygen0`. -/
def expandSReplacement (εPRG : ℝ) : Prop :=
  ∀ D : Bytes 32 → Bytes 32 → RqVec p.l → RqVec p.k → ProbComp Bool,
    |(Pr[= true | do
        let seed ← $ᵗ (Bytes 32)
        let (rho, rhoPrime, key) := prims.expandSeed seed
        let (s1, s2) := prims.expandS rhoPrime
        D rho key s1 s2]).toReal -
      (Pr[= true | do
        let key ← $ᵗ (Bytes 32)
        let rho ← $ᵗ (Bytes 32)
        let s1 ← sampleShortVec p.l p.eta
        let s2 ← sampleShortVec p.k p.eta
        D rho key s1 s2]).toReal| ≤ εPRG

end KeyGen

section Game

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec]

/-- The EUF-NMA game over an arbitrary forging strategy `main` and an arbitrary key generator
`keygen`, observed through the Fiat-Shamir-with-aborts runtime. `main` receives the public key
(but no signing oracle) and returns a candidate `(message, signature)`; the game outputs the
validity bit of the forgery.

Specializing `keygen` to `keygen0` gives the FIPS-keygen NMA game consumed by
`nma_security_fips`. The signature scheme is `FiatShamirWithAbort (identificationScheme …)` at
the seed relation, so `verify` recomputes `Â = ExpandA(pk.ρ)` from the published seed. -/
noncomputable def nmaGame
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    SPMF Bool :=
  (FiatShamirWithAbort.runtime (Commit := Commitment p prims)
    (Chal := CommitHashBytes p) M).evalDist do
      let (pk, _) ← (FiatShamirWithAbort.runtime (Commit := Commitment p prims)
        (Chal := CommitHashBytes p) M).liftProbComp keygen
      let (msg, σ) ← main pk
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ

/-- The advantage of the NMA game with key generator `keygen` is its `true`-probability. The
FIPS-keygen corollary `nma_security_fips` bounds `nmaAdvantage … keygen0` through the short
model. -/
noncomputable def nmaAdvantage
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) : ℝ≥0∞ :=
  Pr[= true | nmaGame p prims hr maxAttempts keygen main]

/-- The EUF-NMA game over the idealized short-key scheme: identical to `nmaGame` except the
signature scheme is `FiatShamirWithAbort` over `identificationSchemeShort`, whose key relation
`validKeyPairShort` is the material-based one that `keygenShort` generates (`hrShort`). The
observed runtime, the forging interface, and the verify recomputation are unchanged. -/
noncomputable def nmaGameShort
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    SPMF Bool :=
  (FiatShamirWithAbort.runtime (Commit := Commitment p prims)
    (Chal := CommitHashBytes p) M).evalDist do
      let (pk, _) ← (FiatShamirWithAbort.runtime (Commit := Commitment p prims)
        (Chal := CommitHashBytes p) M).liftProbComp keygen
      let (msg, σ) ← main pk
      (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify pk msg σ

/-- The advantage of the short-model NMA game with key generator `keygen` is its
`true`-probability. The exact short hop identifies
`|nmaAdvantageShort keygenShort − nmaAdvantageShort keygenShort1|` with the `mldsaMLWEShort`
advantage of `distinguisherBShort`. -/
noncomputable def nmaAdvantageShort
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) : ℝ≥0∞ :=
  Pr[= true | nmaGameShort p prims hr maxAttempts keygen main]

end Game

section Distinguisher

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (TqMatrix p.k p.l)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec]

/-- The random-oracle simulation implementation used by `FiatShamirWithAbort.runtime`: forward
`unifSpec` queries to fresh sampling and answer hash queries through a cached random oracle, all
inside `StateT QueryCache ProbComp`. Running an oracle computation through this implementation
and projecting away the final cache turns it into a plain `ProbComp`, which is what the MLWE
distinguisher must return. -/
noncomputable def roImpl :
    QueryImpl (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp) :=
  unifFwdImpl (M × Commitment p prims →ₒ CommitHashBytes p) +
    (randomOracle : QueryImpl (M × Commitment p prims →ₒ CommitHashBytes p)
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp))

/-- Observe an oracle computation as a plain `ProbComp` by simulating its random oracle from an
empty cache and discarding the final cache state. This is exactly the `ProbComp` underlying
`FiatShamirWithAbort.runtime.evalDist` (see `BundledSemantics.withStateOracle`), exposed so the
MLWE distinguisher — which must inhabit `… → ProbComp Bool` — can run the NMA game internally. -/
noncomputable def simulateToProbComp {α : Type}
    (mx : OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) α) :
    ProbComp α :=
  StateT.run' (simulateQ (roImpl p prims (M := M)) mx) ∅

/-- **The short-secret Module-LWE problem for ML-DSA** (seed-based form). The public challenge
is the matrix seed `ρ` itself (uniform), the secret `s₁` and the additive error `s₂` are uniform
on the `η`-bounded box (`sampleShortVec`), and the decision target is `t = ExpandA(ρ) · s₁ + s₂`
versus uniform `t`. This is the distribution the ML-DSA literature states its MLWE assumption
over; unlike a uniform-error variant it is not information-theoretically trivial, since
`ExpandA(ρ) · s₁ + s₂` with short `(s₁, s₂)` is far from uniform. Bridging the seed-based
challenge to the standard uniform-matrix form is `advantage_mldsaMLWEShort_le_matrix`, under the
explicit `expandAIdealization` assumption. -/
noncomputable def mldsaMLWEShort (p : Params) (prims : Primitives p)
    [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] :
    LearningWithErrors.Problem (Bytes 32) (RqVec p.l) (RqVec p.k) where
  sampleChallenge := $ᵗ (Bytes 32)
  sampleSecret := sampleShortVec p.l p.eta
  sampleError := sampleShortVec p.k p.eta
  noiseless := fun s1 rho => prims.expandA rho * s1
  sampleUniform := $ᵗ (RqVec p.k)

/-- **The matrix-based short Module-LWE problem for ML-DSA.** The standard form: the public
challenge is a uniform matrix `A`, the secret and error are uniform on the `η`-bounded box, and
the decision target is `A · s₁ + s₂` versus uniform. This is the literature-facing hardness
assumption; `mldsaMLWEShort` reduces to it under `expandAIdealization`
(`advantage_mldsaMLWEShort_le_matrix`). -/
noncomputable def mldsaMatrixMLWE (p : Params)
    [SampleableType (TqMatrix p.k p.l)]
    [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] :
    LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k) where
  sampleChallenge := $ᵗ (TqMatrix p.k p.l)
  sampleSecret := sampleShortVec p.l p.eta
  sampleError := sampleShortVec p.k p.eta
  noiseless := fun s1 A => A * s1
  sampleUniform := $ᵗ (RqVec p.k)

/-- **ExpandA idealization (quantified XOF-as-random-matrix step).** For every distinguisher `D`
receiving both the seed and the matrix, the pair `(ρ, ExpandA(ρ))` for uniform `ρ` is
`εA`-indistinguishable from `(ρ, A)` with `A` uniform and independent of `ρ`.

This is the standard random-oracle reading of `ExpandA` (Dilithium's `A = ExpandA(ρ)` with
`ExpandA` modeled as a random function), stated once with inspectable content rather than
supplied per-reduction. For a fixed deterministic `prims.expandA` the unrestricted-quantifier
form is only satisfiable at large `εA` (a distinguisher may recompute `ExpandA(ρ)` and compare);
pending a cost model for the reductions it should be read computationally, against bounded
distinguishers, where it is the assumption that SHAKE-based expansion yields a pseudorandom
matrix. -/
def expandAIdealization (p : Params) (prims : Primitives p)
    [SampleableType (TqMatrix p.k p.l)] (εA : ℝ) : Prop :=
  ∀ [IsUniformSpec unifSpec] (D : Bytes 32 → TqMatrix p.k p.l → ProbComp Bool),
    |(Pr[= true | do
        let rho ← $ᵗ (Bytes 32)
        D rho (prims.expandA rho)]).toReal -
      (Pr[= true | do
        let rho ← $ᵗ (Bytes 32)
        let A ← $ᵗ (TqMatrix p.k p.l)
        D rho A]).toReal| ≤ εA

/-- The short-model MLWE distinguisher: form `pk = (ρ, Power2Round(t).1)` from the challenge
`(ρ, t)`, run the NMA forging strategy `main` on `pk`, simulate the random oracle to verify the
returned forgery, and output the validity bit — typed against the short-secret problem
`mldsaMLWEShort` and the short-key scheme `identificationSchemeShort`. When `(ρ, t)` is real it
reproduces `nmaGameShort … keygenShort`; when `t` is uniform it reproduces
`nmaGameShort … keygenShort1` (`nma_keyswap_hop_short`). -/
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

/-- Lift a seed-based short-MLWE adversary to the uniform-matrix problem: run it on a freshly
sampled seed and the challenged target vector, discarding the matrix. -/
noncomputable def matrixLift
    (B : LearningWithErrors.Adversary (mldsaMLWEShort p prims)) :
    LearningWithErrors.Adversary (mldsaMatrixMLWE p) :=
  fun c => do
    let rho ← $ᵗ (Bytes 32)
    B (rho, c.2)

omit [DecidableEq prims.High] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec] in
/-- **Seed-to-matrix bridge.** Under `expandAIdealization`, any adversary against the seed-based
short problem yields one against the standard uniform-matrix problem: the matrix adversary runs
the seed adversary on a freshly sampled seed and the challenged target vector. The uniform
branches agree exactly (both present an independent uniform `t`), and the real branches differ
by one application of the idealization at the distinguisher
`D ρ A := s₁ ← S_η^ℓ; s₂ ← S_η^k; B (ρ, A·s₁ + s₂)`. -/
lemma advantage_mldsaMLWEShort_le_matrix {εA : ℝ}
    (hA : expandAIdealization p prims εA)
    (B : LearningWithErrors.Adversary (mldsaMLWEShort p prims)) :
    LearningWithErrors.advantage (mldsaMLWEShort p prims) B ≤
      LearningWithErrors.advantage (mldsaMatrixMLWE p) (matrixLift p prims B) + εA := by
  set Bm : LearningWithErrors.Adversary (mldsaMatrixMLWE p) :=
    matrixLift p prims B with hBm
  set D : Bytes 32 → TqMatrix p.k p.l → ProbComp Bool :=
    (fun rho A => do
      let s1 ← sampleShortVec p.l p.eta
      let s2 ← sampleShortVec p.k p.eta
      B (rho, A * s1 + s2)) with hD
  -- Local copy of the generic `advantage = boolDistAdvantage` bridge (its named form lives later
  -- in the file, in the `Hop` section, so it is not yet in scope here).
  have hadv : ∀ {S Sec O : Type} [Add O] (problem : LearningWithErrors.Problem S Sec O)
      (adv : LearningWithErrors.Adversary problem),
      LearningWithErrors.advantage problem adv =
        (LearningWithErrors.game0 problem adv).boolDistAdvantage
          (LearningWithErrors.game1 problem adv) := by
    intro S Sec O _ problem adv
    rw [LearningWithErrors.advantage,
      show LearningWithErrors.experiment problem adv = (do
        let b ← ($ᵗ Bool)
        let z ← if b then LearningWithErrors.game0 problem adv
                      else LearningWithErrors.game1 problem adv
        pure (b == z)) by
        simp only [LearningWithErrors.experiment, LearningWithErrors.game0,
          LearningWithErrors.game1, bind_assoc]]
    exact ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch _ _
  rw [hadv (mldsaMLWEShort p prims) B, hadv (mldsaMatrixMLWE p) Bm,
    ProbComp.boolDistAdvantage, ProbComp.boolDistAdvantage]
  have h1 : Pr[= true | LearningWithErrors.game1 (mldsaMLWEShort p prims) B] =
      Pr[= true | LearningWithErrors.game1 (mldsaMatrixMLWE p) Bm] := by
    simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr, mldsaMLWEShort,
      mldsaMatrixMLWE, hBm, matrixLift, bind_assoc, pure_bind]
    -- Strip the unused leading matrix draw on the right, then commute the two uniform draws.
    rw [probOutput_bind_const, probFailure_uniformSample]
    simp only [tsub_zero, one_mul]
    rw [probOutput_def, probOutput_def,
      DeferredSampling.evalDist_bind_comm ($ᵗ (Bytes 32)) ($ᵗ (RqVec p.k))
        (fun rho t => B (rho, t))]
  have h0 : |(Pr[= true | LearningWithErrors.game0 (mldsaMLWEShort p prims) B]).toReal -
      (Pr[= true | LearningWithErrors.game0 (mldsaMatrixMLWE p) Bm]).toReal| ≤ εA := by
    have hreal : Pr[= true | LearningWithErrors.game0 (mldsaMLWEShort p prims) B] =
        Pr[= true | do let rho ← $ᵗ (Bytes 32); D rho (prims.expandA rho)] := by
      simp only [LearningWithErrors.game0, LearningWithErrors.distr, mldsaMLWEShort, hD,
        bind_assoc, pure_bind]
    have hunif : Pr[= true | LearningWithErrors.game0 (mldsaMatrixMLWE p) Bm] =
        Pr[= true | do
          let rho ← $ᵗ (Bytes 32)
          let A ← $ᵗ (TqMatrix p.k p.l)
          D rho A] := by
      simp only [LearningWithErrors.game0, LearningWithErrors.distr, mldsaMatrixMLWE, hBm,
        matrixLift, hD, bind_assoc, pure_bind]
      -- Commute the trailing `ρ` draw to the front (three independent-draw transpositions).
      rw [probOutput_def, probOutput_def]
      congr 1
      refine Eq.trans (evalDist_bind_congr' _ (fun A => evalDist_bind_congr' _ (fun s1 =>
        DeferredSampling.evalDist_bind_comm (sampleShortVec p.k p.eta) ($ᵗ (Bytes 32))
          (fun s2 rho => B (rho, A * s1 + s2))))) ?_
      refine Eq.trans (evalDist_bind_congr' _ (fun A =>
        DeferredSampling.evalDist_bind_comm (sampleShortVec p.l p.eta) ($ᵗ (Bytes 32))
          (fun s1 rho => sampleShortVec p.k p.eta >>= fun s2 => B (rho, A * s1 + s2)))) ?_
      exact DeferredSampling.evalDist_bind_comm ($ᵗ (TqMatrix p.k p.l)) ($ᵗ (Bytes 32))
        (fun A rho => sampleShortVec p.l p.eta >>= fun s1 =>
          sampleShortVec p.k p.eta >>= fun s2 => B (rho, A * s1 + s2))
    rw [hreal, hunif]
    exact hA D
  rw [h1]
  refine le_trans (abs_sub_le _
    (Pr[= true | LearningWithErrors.game0 (mldsaMatrixMLWE p) Bm].toReal) _) ?_
  rw [add_comm]
  exact add_le_add le_rfl h0

end Distinguisher

section Hop

omit nttOps [DecidableEq prims.High] in
/-- **(Hadv) bias domination, in equality form.** For *any* LWE-style problem and decisional
adversary, the MLWE distinguishing advantage is exactly the Boolean distinguishing advantage
between the two single-branch games `game0` (real distribution) and `game1` (uniform
distribution).

This unfolds `LearningWithErrors.experiment` — `b ← coin; sample ← if b then distr else uniform;
b' ← adv sample; return (b == b')` — into the hidden-bit guessing form
`z ← if b then (distr >>= adv) else (uniform >>= adv); pure (b == z)` and applies
`ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch`. It is fully generic and
discharges the (Hadv) obligation once the NMA games are identified with `game0`/`game1`. -/
theorem advantage_eq_game_boolDistAdvantage
    {Sample Secret Output : Type} [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (adv : LearningWithErrors.Adversary problem) :
    LearningWithErrors.advantage problem adv =
      (LearningWithErrors.game0 problem adv).boolDistAdvantage
        (LearningWithErrors.game1 problem adv) := by
  rw [LearningWithErrors.advantage]
  rw [show (LearningWithErrors.experiment problem adv) =
      (do
        let b ← ($ᵗ Bool)
        let z ← if b then LearningWithErrors.game0 problem adv
                      else LearningWithErrors.game1 problem adv
        pure (b == z)) by
    simp only [LearningWithErrors.experiment, LearningWithErrors.game0,
      LearningWithErrors.game1, bind_assoc]]
  exact ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch _ _

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (CommitHashBytes p)]

omit [SampleableType (RqVec p.k)] in
/-- **NMA-game plumbing.** Pushing the `keygen` sampling out of the Fiat-Shamir-with-aborts
runtime: the `Pr[= true]` of `nmaGame … keygen` equals the `Pr[= true]` of first sampling
`(pk, _) ← keygen` (in plain `ProbComp`) and then running the forge-and-verify tail through
`simulateToProbComp`.

This is the bundled-semantics fact `runtime.evalDist (liftM oa >>= rest) = 𝒟[oa] >>= …`
(`SPMFSemantics.withStateOracle` interpret/observe with `roSim.run'_liftM_bind`), specialised to
the ML-DSA NMA game; it reduces game comparisons to comparing the *key distributions* only, with
all the runtime plumbing already discharged. `nma_security_fips` uses it to expose the `keygen0`
game to the `expandSReplacement` distinguisher. -/
theorem nmaGame_eq_keygen_bind
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    nmaGame p prims hr maxAttempts keygen main =
      𝒟[(do
        let (pk, _) ← keygen
        simulateToProbComp p prims (M := M) (do
          let (msg, σ) ← main pk
          (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
            pk msg σ))] := by
  classical
  let ro : QueryImpl (M × Commitment p prims →ₒ CommitHashBytes p)
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp) := randomOracle
  let impl : QueryImpl (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp) :=
    unifFwdImpl (M × Commitment p prims →ₒ CommitHashBytes p) + ro
  let rest : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) Bool := fun pk => do
    let (msg, σ) ← main pk
    (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ
  unfold nmaGame FiatShamirWithAbort.runtime ProbCompRuntime.evalDist
    ProbCompRuntime.liftProbComp SPMFSemantics.evalDist SemanticsVia.denote
  change 𝒟[(simulateQ impl (liftM keygen >>= fun pk => rest pk.1)).run' ∅] =
    𝒟[keygen >>= fun pk => simulateToProbComp p prims (rest pk.1)]
  rw [simulateQ_bind,
    roSim.run'_liftM_bind (ro := ro) (oa := keygen)
      (rest := fun pk => simulateQ impl (rest pk.1)) (s := ∅)]
  rw [evalDist_bind, evalDist_bind]
  simp only [simulateToProbComp, roImpl]
  rfl

omit [SampleableType (RqVec p.k)] in
/-- Short-model NMA-game / distinguisher plumbing: the `nmaGame_eq_keygen_bind` rewrite at the
short scheme. Pushing the `keygen` sampling out of the Fiat-Shamir-with-aborts runtime, the
`Pr[= true]` of `nmaGameShort … keygen` equals that of first sampling `(pk, _) ← keygen` in plain
`ProbComp` and then running the forge-and-verify tail through `simulateToProbComp` — exactly the
body of `distinguisherBShort` evaluated at `pk`. -/
theorem nmaGameShort_eq_keygen_bind
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    nmaGameShort p prims hr maxAttempts keygen main =
      𝒟[(do
        let (pk, _) ← keygen
        simulateToProbComp p prims (M := M) (do
          let (msg, σ) ← main pk
          (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify
            pk msg σ))] := by
  classical
  let ro : QueryImpl (M × Commitment p prims →ₒ CommitHashBytes p)
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp) := randomOracle
  let impl : QueryImpl (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
      (StateT ((M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ProbComp) :=
    unifFwdImpl (M × Commitment p prims →ₒ CommitHashBytes p) + ro
  let rest : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) Bool := fun pk => do
    let (msg, σ) ← main pk
    (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify pk msg σ
  unfold nmaGameShort FiatShamirWithAbort.runtime ProbCompRuntime.evalDist
    ProbCompRuntime.liftProbComp SPMFSemantics.evalDist SemanticsVia.denote
  change 𝒟[(simulateQ impl (liftM keygen >>= fun pk => rest pk.1)).run' ∅] =
    𝒟[keygen >>= fun pk => simulateToProbComp p prims (rest pk.1)]
  rw [simulateQ_bind,
    roSim.run'_liftM_bind (ro := ro) (oa := keygen)
      (rest := fun pk => simulateQ impl (rest pk.1)) (s := ∅)]
  rw [evalDist_bind, evalDist_bind]
  simp only [simulateToProbComp, roImpl]
  rfl

/-- **The exact short-model key-swap hop (Lemma 7, Step 1).** Against the idealized key
generators `keygenShort` / `keygenShort1`, the short-model NMA-game gap **is** the
`mldsaMLWEShort` distinguishing advantage of `distinguisherBShort` — both branch identifications
are pure monad-rewriting identities, with no statistical slack: the key generators sample
`ρ`, `K`, `s₁`, `s₂` independently, exactly as the problem's `distr` / `uniformDistr` do (the
unused `K` draw strips off, being the leading draw).

Both branches follow the same shape: rewrite the game through `nmaGameShort_eq_keygen_bind`,
unfold the matching MLWE branch, strip the leading `K` draw with `probOutput_bind_const`
(`Pr[⊥ | $ᵗ (Bytes 32)] = 0`), and — in the uniform branch — the unused `s₁`, `s₂` draws. -/
theorem nma_keyswap_hop_short
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    |(nmaAdvantageShort p prims hr maxAttempts (keygenShort p prims) main).toReal -
        (nmaAdvantageShort p prims hr maxAttempts (keygenShort1 p prims) main).toReal| ≤
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
        (distinguisherBShort p prims hr maxAttempts main) := by
  set B := distinguisherBShort p prims hr maxAttempts main (M := M) with hB
  -- `Pr[= true | 𝒟[Y]] = Pr[= true | Y]` holds definitionally (the SPMF self-lift is `id`).
  have peel : ∀ (Y : ProbComp Bool), Pr[= true | 𝒟[Y]] = Pr[= true | Y] := fun _ => rfl
  have hkey : Pr[⊥ | ($ᵗ (Bytes 32) : ProbComp (Bytes 32))] = 0 := probFailure_uniformSample _
  have hss : ∀ (k b : ℕ) [SampleableType (RqVec k)], Pr[⊥ | sampleShortVec k b] = 0 := by
    intro k b _
    simp only [sampleShortVec, probFailure_map, probFailure_uniformSample]
  rw [advantage_eq_game_boolDistAdvantage (mldsaMLWEShort p prims) B,
    ProbComp.boolDistAdvantage, nmaAdvantageShort, nmaAdvantageShort]
  have hH1 : Pr[= true | nmaGameShort p prims hr maxAttempts (keygenShort1 p prims) main] =
      Pr[= true | LearningWithErrors.game1 (mldsaMLWEShort p prims) B] := by
    rw [nmaGameShort_eq_keygen_bind]
    simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr, hB,
      distinguisherBShort, mldsaMLWEShort, keygenShort1, keyFromMaterial, bind_assoc, pure_bind]
    -- Strip the unused leading `key` draw, then the unused `s₁`, `s₂` draws under `ρ`.
    rw [peel, probOutput_bind_const, hkey]
    simp only [tsub_zero, one_mul]
    refine probOutput_bind_congr' _ true (fun rho => ?_)
    rw [probOutput_bind_const, hss, probOutput_bind_const, hss]
    simp only [tsub_zero, one_mul]
  have hH0 : Pr[= true | nmaGameShort p prims hr maxAttempts (keygenShort p prims) main] =
      Pr[= true | LearningWithErrors.game0 (mldsaMLWEShort p prims) B] := by
    rw [nmaGameShort_eq_keygen_bind]
    simp only [LearningWithErrors.game0, LearningWithErrors.distr, hB, distinguisherBShort,
      mldsaMLWEShort, keygenShort, keyFromMaterial, bind_assoc, pure_bind]
    -- Only the leading `key` draw is unused here (`s₁`, `s₂` build `t`).
    rw [peel, probOutput_bind_const, hkey]
    simp only [tsub_zero, one_mul]
  rw [hH0, hH1]

end Hop

section Extractor

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (CommitHashBytes p)]

/-- **The SelfTargetMSIS problem embedded by ML-DSA verification in the idealized short-key
model (Lemma 7, Step 3).**

After the key has uniform `t` (`keygenShort1`), a forgery `(msg, some (w', (z, h)))` accepted by
`verify` is, via the random oracle answer `c̃ = H(msg, w')`, a SelfTargetMSIS solution: the
matrix `Â = ExpandA(ρ)` is the challenge, the public key `pk` is the target, the hash input is
`(msg, w')`, and the response is `(z, h)`. Validity recomputes the commitment from
`(pk, c̃, (z, h))` via `UseHint ∘ computeWApprox` (commitment recoverability) and runs the
identification-scheme verifier; this is precisely the equation `verify` checks, so an accepted
forgery maps to a valid STMSIS solution.

The `sampleParams` draws the same idealized short key as `keygenShort1` / `mldsaMLWEShort`: the
matrix seed `ρ`, the signing key `K`, and the short secrets are drawn independently, `t` is
uniform, and the published pair is `(ExpandA(ρ), pk)` with `pk = ⟨ρ, Power2Round(t).1⟩`. -/
noncomputable def mldsaSTMSISShort (M : Type) :
    SelfTargetMSIS.Problem (TqMatrix p.k p.l) (Response p prims) (PublicKey p prims)
      (M × Commitment p prims) (CommitHashBytes p) where
  sampleParams := do
    let (pk, _) ← keygenShort1 p prims
    return (prims.expandA pk.rho, pk)
  isValid := fun aHat pk cTilde (z, h) =>
    -- Recover the commitment `w'` from `(pk, c̃, (z, h))` and run the identification verifier.
    let w' := prims.useHintVec h (computeWApprox p prims aHat (prims.sampleInBall cTilde) z pk.t1)
    (identificationSchemeShort p prims).verify pk w' cTilde (z, h)

/-- **The SelfTargetMSIS extractor `C` for the idealized short-key model (Lemma 7, Step 3).**

`C` runs the NMA forger `main` on the public key `pk` (the STMSIS target). The forger interacts
with the random oracle `H : (M × Commitment) →ₒ CommitHashBytes`. On a forgery
`(msg, some (w', (z, h)))` `C` outputs the STMSIS preimage `(msg, w')` together with the response
`(z, h)`. An aborting forgery `(msg, none)` is mapped to a dummy preimage with a zeroed response,
which the STMSIS RO-consistency check rejects. The matrix in `params.1` is ignored by `C` (it
equals `ExpandA(params.2.ρ)`).

The STMSIS experiment then looks up `c̃ = H(msg, w')` in the oracle cache and checks
`mldsaSTMSISShort.isValid Â pk c̃ (z, h)`, which recomputes `w'` from `(pk, c̃, (z, h))` and runs
the identification verifier — exactly what the NMA `verify` does after querying `H(msg, w')`. -/
noncomputable def extractorCShort [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    SelfTargetMSIS.Adversary (mldsaSTMSISShort p prims M) where
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
      -- Aborting forgery: no valid preimage. Emit a dummy that fails RO consistency / `isValid`.
      return ((msg, default), default)

/-- **Per-key STMSIS read-back comparison, short model.** For a fixed public key `pk`, the
short-model NMA forge-and-verify tail (run through `simulateToProbComp`) accepts no more often
than the SelfTargetMSIS experiment tail of `extractorCShort` at the matching parameters
`(ExpandA(ρ), pk)`.

The argument never inspects the key relation. Both tails first simulate `main pk` against the
same random oracle from the empty cache; the proof compares them after that shared prefix
(`probOutput_bind_mono`). On an aborting forgery the NMA tail is deterministically `false`. On a
forgery `some (w', (z, h))` both branches issue the *same* `H(msg, w')` query on the *same*
cache, so the random answer `c̃` and the resulting cache coincide; the STMSIS experiment then
reads `c̃` back and `mldsaSTMSISShort.isValid` recovers `w'` as exactly the `useHintVec …` value
that `verify` checks against, so an accepted NMA forgery is a valid STMSIS solution. -/
private theorem stmsis_tail_le_short
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims)))
    (pk : PublicKey p prims) :
    Pr[= true | simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← main pk
        (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts).verify
          pk msg σ)] ≤
      Pr[= true | do
        let ((hashInput, response), cache) ←
          (simulateQ (roImpl p prims (M := M))
            ((extractorCShort p prims main).run (prims.expandA pk.rho, pk))).run ∅
        match cache hashInput with
        | some hashOutput =>
            pure ((mldsaSTMSISShort p prims M).isValid (prims.expandA pk.rho) pk
              hashOutput response)
        | none => pure false] := by
  classical
  -- Decompose both tails over the shared simulation of `main pk` from the empty cache.
  unfold simulateToProbComp extractorCShort
  simp only [bind_pure_comp, simulateQ_bind, StateT.run_bind, StateT.run'_eq, map_bind,
    bind_assoc]
  -- Compare after the shared `main pk` simulation prefix.
  refine probOutput_bind_mono fun a _ => ?_
  -- `a = ((msg, σ), cache₀)`; split on whether the forgery aborts.
  obtain ⟨⟨msg, σ⟩, cache0⟩ := a
  cases σ with
  | none =>
    -- Aborting forgery: NMA `verify` is deterministically `false`, so the NMA tail has weight `0`.
    simp only [FiatShamirWithAbort, simulateQ_pure, StateT.run_pure, map_pure,
      probOutput_pure]
    simp
  | some wzh =>
    obtain ⟨w', z, h⟩ := wzh
    -- Non-aborting forgery `(w', (z, h))`. Both branches issue the same `H(msg, w')` query on
    -- `cache0`; reduce the NMA `verify` and the extractor body to that single query.
    simp only [FiatShamirWithAbort, simulateQ_map, StateT.run_map, bind_pure_comp]
    -- Both sides are now `f <$> (simulateQ roImpl (query (msg, w'))).run cache0`; turn the maps
    -- into binds over the shared random-oracle run and compare per random answer `(c, cache₁)`.
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    refine probOutput_bind_mono fun cc hcc => ?_
    simp only [pure_bind]
    -- The query simulation caches its answer: `cc.2 (msg, w') = some cc.1`.
    have hquery : simulateQ (roImpl p prims (M := M)) (query (msg, w') :
          OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) _) =
        (randomOracle : QueryImpl (M × Commitment p prims →ₒ CommitHashBytes p) _) (msg, w') :=
      roSim.simulateQ_liftM_spec_query _ _
    rw [hquery] at hcc
    have hcache : cc.2 (msg, w') = some cc.1 := by
      cases hc0 : cache0 (msg, w') with
      | some u =>
        rw [randomOracle, QueryImpl.withCaching_run_some _ hc0, support_pure,
          Set.mem_singleton_iff] at hcc
        subst hcc; exact hc0
      | none =>
        rw [randomOracle, QueryImpl.withCaching_run_none _ hc0, support_map] at hcc
        obtain ⟨u, _, hu⟩ := hcc
        subst hu
        exact QueryCache.cacheQuery_self _ (msg, w') u
    rw [hcache]
    -- An accepted NMA forgery is a valid STMSIS solution (commitment recoverability is exactly the
    -- middle conjunct of `verify`, which `isValid` discharges by `decide (X = X)`).
    rw [probOutput_pure, probOutput_pure]
    by_cases hverify :
        (identificationSchemeShort p prims).verify pk w' cc.1 (z, h) = true
    · -- Accepted: `isValid` recovers `w'` as the very `useHintVec …` value `verify` checks against,
      -- so its middle conjunct is `decide (X = X) = true` and `isValid = true`.
      have hvalid :
          (mldsaSTMSISShort p prims M).isValid (prims.expandA pk.rho) pk cc.1 (z, h) = true := by
        simp only [mldsaSTMSISShort, identificationSchemeShort, identificationScheme]
          at hverify ⊢
        revert hverify
        grind
      rw [if_pos hverify.symm, if_pos hvalid.symm]
    · simp only [Bool.not_eq_true] at hverify
      rw [hverify]
      simp

/-- **The SelfTargetMSIS extraction bound in the idealized short-key model (Lemma 7, Step 3).**
The uniform-`t` short-model EUF-NMA advantage (key generator `keygenShort1`) is bounded by the
SelfTargetMSIS advantage of the extractor against `mldsaSTMSISShort`.

A forgery accepted by the NMA game (after the `H(msg, w')` query inside `verify`) is exactly a
valid SelfTargetMSIS solution for `mldsaSTMSISShort`: the extractor reproduces the forger's
oracle trace, the experiment's RO-consistency lookup recovers the same `c̃ = H(msg, w')`, and
`isValid` recovers `w'` and runs the identical verifier. The reduction to the per-key comparison
`stmsis_tail_le_short` is the bundled-semantics rewrite (`nmaGameShort_eq_keygen_bind`) plus
monotonicity over the shared `keygenShort1` prefix — the short problem's `sampleParams` is
definitionally `keygenShort1` followed by publishing `(ExpandA(ρ), pk)`. -/
theorem nmaAdvantage_keygenShort1_le_stmsis
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    nmaAdvantageShort p prims hr maxAttempts (keygenShort1 p prims) main ≤
      SelfTargetMSIS.advantage (extractorCShort p prims main) := by
  classical
  rw [nmaAdvantageShort, nmaGameShort_eq_keygen_bind, SelfTargetMSIS.advantage,
    SelfTargetMSIS.experiment]
  rw [probOutput_def, SPMF.evalDist_def]
  -- The short STMSIS `sampleParams` is exactly `keygenShort1` followed by publishing
  -- `(ExpandA(ρ), pk)`, so both `Pr[= true]`s bind over the same prefix; compare them per-key.
  change Pr[= true | (keygenShort1 p prims) >>= _] ≤
    Pr[= true | ((mldsaSTMSISShort p prims M).sampleParams) >>= _]
  rw [show (mldsaSTMSISShort p prims M).sampleParams =
      (keygenShort1 p prims) >>= fun pkSk => pure (prims.expandA pkSk.1.rho, pkSk.1) from rfl]
  rw [bind_assoc]
  refine probOutput_bind_mono ?_
  rintro ⟨pk, sk⟩ _
  rw [pure_bind]
  convert stmsis_tail_le_short p prims hr maxAttempts main pk using 2
  rw [roImpl, unifFwdImpl]
  refine bind_congr fun x => ?_
  obtain ⟨⟨hashInput, response⟩, cache⟩ := x
  dsimp only
  cases cache hashInput <;> rfl

end Extractor

end NMA

open NMA

section Headline

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]
  {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (CommitHashBytes p)]

open scoped Classical in
/-- **NMA security of ML-DSA in the idealized short-key model (Lemma 7, CRYPTO 2023).**

For every EUF-NMA adversary `A` against the ML-DSA scheme (instantiated via `FiatShamirWithAbort`
over the idealized short-secret key generation `keygenShort`), there exist an MLWE adversary `B`
and a SelfTargetMSIS adversary `C` such that

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C)`.

The reductions are the concrete ones built in this file: the key-swap distinguisher
`distinguisherBShort`, whose `mldsaMLWEShort` advantage **equals** the real-vs-uniform key gap —
the short key-swap hop `nma_keyswap_hop_short` is an exact monad identity, so no statistical
slack term appears in the bound — and the SelfTargetMSIS extractor `extractorCShort`, which turns
a uniform-`t` forgery into a short self-target solution
(`nmaAdvantage_keygenShort1_le_stmsis`).

The hypothesis `hMlweBridge` supplies, for every forging strategy, an abstract MLWE adversary at
a bridge slack `εbridge` against the seed-based short problem `mldsaMLWEShort` — the distribution
the ML-DSA Module-LWE assumption is stated over (secret and error uniform on the `η`-bounded
box). Its canonical discharge lands on the uniform-matrix problem: take `mlwe := mldsaMatrixMLWE
p`, `εbridge := εA`, and for each `main` the witness
`matrixLift p prims (distinguisherBShort p prims hr maxAttempts main)` with the proven reduction
`advantage_mldsaMLWEShort_le_matrix` under the `expandAIdealization εA` assumption.

The SelfTargetMSIS side has matching types, so `hStmsis` is a plain equality
`stmsis = mldsaSTMSISShort p prims M`, and `hGen : hr.gen = keygenShort p prims` pins the
Fiat-Shamir key generation to the idealized short-key generator. The relation of `hr` is the
material-based `validKeyPairShort`, which `keygenShort` genuinely generates: the pair
`(hr, hGen)` is inhabited by `hrShort` (`keygenShort_generable`), so the statement has
non-vacuous instances.

This is the EUF-NMA half (Lemma 7) of the ML-DSA security proof in the idealized short-key model;
the FIPS-keygen transfer is `nma_security_fips`. -/
theorem nma_security_short
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGen : hr.gen = keygenShort p prims)
    (hStmsis : stmsis = mldsaSTMSISShort p prims M)
    (εbridge : ℝ)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      ∃ B : LearningWithErrors.Adversary mlwe,
        LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hr maxAttempts main) ≤
          LearningWithErrors.advantage mlwe B + εbridge) :
    ∀ (adv : SignatureAlg.eufNmaAdv
      (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts)),
    ∃ (mlweReduction : LearningWithErrors.Adversary mlwe)
      (stmsisReduction : SelfTargetMSIS.Adversary stmsis),
      adv.advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal (LearningWithErrors.advantage mlwe mlweReduction + εbridge) +
        SelfTargetMSIS.advantage stmsisReduction := by
  classical
  intro adv
  obtain ⟨B, hB⟩ := hMlweBridge adv.main
  subst hStmsis
  refine ⟨B, extractorCShort p prims adv.main, ?_⟩
  -- The EUF-NMA experiment is the real-`t` short-model NMA game with `main := adv.main`.
  have hadv : adv.advantage (FiatShamirWithAbort.runtime
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) =
      nmaAdvantageShort p prims hr maxAttempts (keygenShort p prims) adv.main := by
    rw [SignatureAlg.eufNmaAdv.advantage, nmaAdvantageShort, nmaGameShort]
    rw [SignatureAlg.eufNmaExp]
    simp only [FiatShamirWithAbort, hGen]
    rfl
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
  have hg0 : nmaAdvantageShort p prims hr maxAttempts (keygenShort p prims) adv.main =
      Pr[= true | pc0] := by
    rw [nmaAdvantageShort, nmaGameShort_eq_keygen_bind, probOutput_def, probOutput_def,
      SPMF.evalDist_def]
  have hg1 : nmaAdvantageShort p prims hr maxAttempts (keygenShort1 p prims) adv.main =
      Pr[= true | pc1] := by
    rw [nmaAdvantageShort, nmaGameShort_eq_keygen_bind, probOutput_def, probOutput_def,
      SPMF.evalDist_def]
  -- Triangle bound: real game ≤ uniform game + MLWE advantage.
  have htri := ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage pc0 pc1
  rw [hg0]
  refine le_trans htri ?_
  -- `pc0.boolDistAdvantage pc1 = |nmaAdv keygenShort - nmaAdv keygenShort1|`, which the exact
  -- short key-swap hop bounds by the `mldsaMLWEShort` advantage — no statistical slack.
  have hbias : pc0.boolDistAdvantage pc1 ≤
      LearningWithErrors.advantage (mldsaMLWEShort p prims)
        (distinguisherBShort p prims hr maxAttempts adv.main) := by
    have hk := nma_keyswap_hop_short p prims hr maxAttempts (M := M) adv.main
    rw [ProbComp.boolDistAdvantage, ← hg0, ← hg1]
    exact hk
  -- STMSIS extraction bound on the uniform game.
  have hstm := nmaAdvantage_keygenShort1_le_stmsis p prims hr maxAttempts (M := M) adv.main
  rw [hg1] at hstm
  calc Pr[= true | pc1] + ENNReal.ofReal (pc0.boolDistAdvantage pc1)
      ≤ SelfTargetMSIS.advantage (extractorCShort p prims adv.main) +
        ENNReal.ofReal (LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hr maxAttempts adv.main)) :=
        add_le_add hstm (ENNReal.ofReal_le_ofReal hbias)
    _ ≤ SelfTargetMSIS.advantage (extractorCShort p prims adv.main) +
        ENNReal.ofReal (LearningWithErrors.advantage mlwe B + εbridge) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal (le_trans hB le_rfl))
    _ = ENNReal.ofReal (LearningWithErrors.advantage mlwe B + εbridge) +
        SelfTargetMSIS.advantage (extractorCShort p prims adv.main) := add_comm _ _

open scoped Classical in
/-- **NMA security of ML-DSA at the FIPS seed-derived key generation.**

The short-model bound `nma_security_short` transferred to the deterministic FIPS key generator
`keygen0` through the XOF-replacement assumption `expandSReplacement`: for every EUF-NMA
adversary against the ML-DSA scheme instantiated with the seed-derived key relation
(`hGen : hr.gen = keygen0 p prims`, inhabited by `hrFips` / `keygen0_generable`), there are an
MLWE adversary and a SelfTargetMSIS adversary with

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C) + εPRG`.

The proof has exactly one new ingredient beyond the short model: the FIPS and short NMA games
share their forge-and-verify tail (`identificationScheme` and `identificationSchemeShort` carry
the same `verify` function), so the gap between the `keygen0` game and the `keygenShort` game is
one application of `hPRG` at the distinguisher `D ρ K s₁ s₂ :=` "run the tail at the key built by
`keyFromMaterial` from the material `(ρ, K, s₁, s₂)`": its real branch is exactly the FIPS game
and its ideal branch is exactly the short game. The short-model reduction hypotheses
(`hrS`/`hGenS`, `hStmsis`, `hMlweBridge`) then bound the short game as in `nma_security_short`,
applied to the same forging strategy repackaged at the short scheme tag. -/
theorem nma_security_fips
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hrS : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGenS : hrS.gen = keygenShort p prims)
    (hStmsis : stmsis = mldsaSTMSISShort p prims M)
    (εPRG : ℝ) (hPRG : expandSReplacement p prims εPRG)
    (εbridge : ℝ)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      ∃ B : LearningWithErrors.Adversary mlwe,
        LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hrS maxAttempts main) ≤
          LearningWithErrors.advantage mlwe B + εbridge) :
    ∀ (adv : SignatureAlg.eufNmaAdv
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts)),
    ∃ (mlweReduction : LearningWithErrors.Adversary mlwe)
      (stmsisReduction : SelfTargetMSIS.Adversary stmsis),
      adv.advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal (LearningWithErrors.advantage mlwe mlweReduction + εbridge) +
        SelfTargetMSIS.advantage stmsisReduction +
        ENNReal.ofReal εPRG := by
  classical
  intro adv
  obtain ⟨mlweRed, stmsisRed, hshortBound⟩ :=
    nma_security_short p prims mlwe stmsis maxAttempts hrS hGenS hStmsis εbridge hMlweBridge
      ⟨adv.main⟩
  refine ⟨mlweRed, stmsisRed, ?_⟩
  -- The FIPS EUF-NMA experiment is the real-`t` NMA game at `keygen0` with `main := adv.main`.
  have hadv : adv.advantage (FiatShamirWithAbort.runtime
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) =
      nmaAdvantage p prims hr maxAttempts (keygen0 p prims) adv.main := by
    rw [SignatureAlg.eufNmaAdv.advantage, nmaAdvantage, nmaGame]
    rw [SignatureAlg.eufNmaExp]
    simp only [FiatShamirWithAbort, hGen]
    rfl
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
      Pr[= true | pcF] := by
    rw [nmaAdvantage, nmaGame_eq_keygen_bind, probOutput_def, probOutput_def, SPMF.evalDist_def]
  have hgS : (⟨adv.main⟩ : SignatureAlg.eufNmaAdv
      (FiatShamirWithAbort (identificationSchemeShort p prims) hrS M maxAttempts)).advantage
        (FiatShamirWithAbort.runtime
          (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) =
      Pr[= true | pcS] := by
    have h1 : (⟨adv.main⟩ : SignatureAlg.eufNmaAdv
        (FiatShamirWithAbort (identificationSchemeShort p prims) hrS M maxAttempts)).advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) =
        nmaAdvantageShort p prims hrS maxAttempts (keygenShort p prims) adv.main := by
      rw [SignatureAlg.eufNmaAdv.advantage, nmaAdvantageShort, nmaGameShort]
      rw [SignatureAlg.eufNmaExp]
      simp only [FiatShamirWithAbort, hGenS]
      rfl
    rw [h1, nmaAdvantageShort, nmaGameShort_eq_keygen_bind, probOutput_def, probOutput_def,
      SPMF.evalDist_def]
  -- The PRG hop: the two games are the two branches of `hPRG` at the shared verify tail.
  have hF : Pr[= true | pcF] = Pr[= true | do
      let seed ← $ᵗ (Bytes 32)
      let (rho, rhoPrime, _key) := prims.expandSeed seed
      let (s1, s2) := prims.expandS rhoPrime
      simulateToProbComp p prims (M := M) (do
        let d ← adv.main ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2)] := by
    rw [hpcF]
    simp only [keygen0, keyFromMaterial, bind_assoc, pure_bind]
  have hS : Pr[= true | pcS] = Pr[= true | do
      let _key ← $ᵗ (Bytes 32)
      let rho ← $ᵗ (Bytes 32)
      let s1 ← sampleShortVec p.l p.eta
      let s2 ← sampleShortVec p.k p.eta
      simulateToProbComp p prims (M := M) (do
        let d ← adv.main ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2)] := by
    rw [hpcS]
    simp only [keygenShort, keyFromMaterial, bind_assoc, pure_bind]
    rfl
  have hbias : pcF.boolDistAdvantage pcS ≤ εPRG := by
    rw [ProbComp.boolDistAdvantage, hF, hS]
    exact hPRG (fun rho _key s1 s2 => simulateToProbComp p prims (M := M) (do
      let d ← adv.main ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
        ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2))
  -- Assemble: FIPS game ≤ short game + εPRG ≤ (MLWE + εbridge) + STMSIS + εPRG.
  rw [hadv, hgF]
  refine le_trans (ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage pcF pcS) ?_
  have hshort' : Pr[= true | pcS] ≤
      ENNReal.ofReal (LearningWithErrors.advantage mlwe mlweRed + εbridge) +
        SelfTargetMSIS.advantage stmsisRed := by
    rw [← hgS]
    exact hshortBound
  exact add_le_add hshort' (ENNReal.ofReal_le_ofReal hbias)

end Headline

/-! ## Status

**Short-secret, seed-based MLWE.** `mldsaMLWEShort` draws both the secret `s₁` and the error
`s₂` from the `η`-bounded box via `sampleShortVec`, and phrases the public challenge as the
matrix *seed* `ρ` with the matrix defined on demand as `ExpandA(ρ)`; `distinguisherBShort`
consumes `(ρ, t)` directly and is total. The headline `nma_security_short` and its FIPS transfer
`nma_security_fips` are proven and assembled from:

1. **The exact key-swap hop (`nma_keyswap_hop_short`).** `(Hadv)` is
   `advantage_eq_game_boolDistAdvantage`; both branch identifications are pure runtime-plumbing
   rewrites through `nmaGameShort_eq_keygen_bind`. Because `keygenShort` / `keygenShort1` sample
   `ρ`, `K`, `s₁`, `s₂` independently — exactly as `mldsaMLWEShort`'s `distr` / `uniformDistr` do
   — the hop is an *equality*, with no statistical slack term.

2. **STMSIS extraction (`nmaAdvantage_keygenShort1_le_stmsis`).** Both `Pr[= true]`s reduce,
   through the shared `withStateOracle` semantics, to: sample the uniform-`t` key, run the forger
   against the RO, and on `some (w', (z,h))` read `c̃ = H(msg, w')` from the cache and accept iff
   `ids.verify pk w' c̃ (z,h)`. After `nmaGameShort_eq_keygen_bind` both sides bind over the same
   `keygenShort1` prefix, so `probOutput_bind_mono` reduces to the per-key lemma
   `stmsis_tail_le_short`, which decomposes both tails over the shared `main pk` simulation,
   gives weight `0` to the aborting branch, and on a non-aborting forgery couples the single
   `H(msg, w')` query — the cached answer is read back
   (`QueryImpl.withCaching_run_some`/`_none`, `QueryCache.cacheQuery_self`) and
   `verify = true → isValid = true` (the middle `decide (X = X)` conjunct) closes the per-answer
   inequality.

3. **FIPS transfer (`nma_security_fips`).** The FIPS and short games share their
   forge-and-verify tail, so their gap is one application of `expandSReplacement` at the tail
   viewed as a distinguisher on the key material `(ρ, K, s₁, s₂)`. The ideal branch of that
   assumption is short sampling — the FIPS marginals of `ExpandS` — not full-ring uniformity.

4. **Bridges to the abstract problems.** `nma_security_short` quantifies over an *abstract*
   `mlwe`, an *abstract* `stmsis`, and an *abstract* `hr`, while the reductions here are against
   the *concrete* `mldsaMLWEShort` / `mldsaSTMSISShort` and `keygenShort`/`keygenShort1`. The
   bridge hypotheses are part of the statement: `hGen : hr.gen = keygenShort p prims` (inhabited
   by `hrShort`, `keygenShort_generable`), `hStmsis : stmsis = mldsaSTMSISShort p prims M`, and
   `hMlweBridge` at slack `εbridge`. The canonical discharge of `hMlweBridge` is
   `advantage_mldsaMLWEShort_le_matrix`: under `expandAIdealization εA` the seed-based problem
   reduces to the standard uniform-matrix `mldsaMatrixMLWE` at `εbridge := εA`, with the witness
   `matrixLift (distinguisherBShort …)`.
-/

end MLDSA
