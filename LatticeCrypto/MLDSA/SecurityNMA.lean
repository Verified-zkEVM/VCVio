/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import LatticeCrypto.MLDSA.Security

/-!
# ML-DSA EUF-NMA Security: the MLWE key-swap hop (Lemma 7, Step 1)

This file builds the reduction infrastructure for the ML-DSA EUF-NMA security theorem
`MLDSA.nma_security` (issue #227, the real Dilithium Lemma 7), covering the **MLWE key-swap hop**
and the **SelfTargetMSIS extractor**:

1. **MLWE key-swap (`nma_keyswap_hop`).** Replace the honest key generation, where the public key
   vector is `t = Â · s₁ + s₂`, with a variant `keygen1` that samples `t` uniformly. The gap
   between the two EUF-NMA games equals the decisional MLWE advantage of the (seed-based)
   distinguisher `B = distinguisherB`. The `(Hadv)` and uniform-branch `(H1)` parts are pure
   runtime-plumbing rewrites; the real-branch `(H0)` is discharged from the honest-sampling field
   `Primitives.Laws.expandS_honest_sampling` (the ROM idealization of `ExpandSeed`/`ExpandS`).
2. **SelfTargetMSIS extraction (`nmaAdvantage_keygen1_le_stmsis`).** Once `t` is uniform the key
   carries no secret, so a forgery is a short vector satisfying the SelfTargetMSIS relation; the
   extractor `extractorC` reads `(z, c̃)` out of the forged signature. This is fully proven: the
   shared random-oracle simulation lines up the NMA `verify` query with the extractor's RO read-back
   (`stmsis_tail_le`), and an accepted forgery is a valid SelfTargetMSIS solution by commitment
   recoverability.

The `H₁` reprogramming step of the paper folds into the random-oracle modeling and is not separated
out here. `MLDSA.nma_security` assembles the two steps under the bridge hypotheses negotiated in its
statement (`hGen`, `hStmsis`, `hMlweBridge`).

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
no embedding. The `MlweEmbedding` record is therefore gone.
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

omit [DecidableEq prims.High] [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] in
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
slack); the deterministic-XOF derivation is not part of this hop and is handled
separately by a named XOF-replacement assumption. -/

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
`S_b^k = { v : RqVec k | ‖v‖∞ ≤ b }`, i.e. every coefficient of every component
uniform on the centered interval `[-b, b]`. This is the secret/error
distribution of the Module-LWE assumption used by ML-DSA (`η ∈ {2, 4}` for the
approved parameter sets). -/
noncomputable def sampleShortVec (k b : ℕ) [SampleableType (RqVec k)] : ProbComp (RqVec k) :=
  letI : Fintype {v : RqVec k // polyVecBounded v b} := .ofFinite _
  letI : Nonempty {v : RqVec k // polyVecBounded v b} := ⟨0, polyVecBounded_zero k b⟩
  letI : SampleableType {v : RqVec k // polyVecBounded v b} := .ofFintype _
  Subtype.val <$> ($ᵗ {v : RqVec k // polyVecBounded v b})

/-- **Idealized key generation (real `t`).** Sample the matrix seed `ρ`, the
signing key `K`, and the short secrets `(s₁, s₂)` independently — `(s₁, s₂)`
uniform on the `η`-bounded box — and form `t = ExpandA(ρ) · s₁ + s₂`. This is
the honestly-sampled key distribution of the idealized proof-level ML-DSA
model; the deterministic seed-expanded `keygen0` is related to it by a separate
XOF-replacement assumption. -/
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

omit [DecidableEq prims.High] in
/-- **Satisfiability certificate for the short-model `hGen` hypothesis.** Some generable
relation over `validKeyPairShort` has `keygenShort` as its generator — witnessed by
`hrShort`. The short-model security statements hypothesize such a relation via
`hGen : hr.gen = keygenShort p prims`; this theorem records that the hypothesis pair
`(hr, hGen)` is inhabited, so those statements have non-vacuous instances. -/
theorem keygenShort_generable :
    ∃ hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims),
      hr.gen = keygenShort p prims :=
  ⟨hrShort p prims, rfl⟩

end KeyGen

section Game

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec]

/-- The EUF-NMA game over an arbitrary forging strategy `main` and an arbitrary key generator
`keygen`, observed through the Fiat-Shamir-with-aborts runtime. `main` receives the public key
(but no signing oracle) and returns a candidate `(message, signature)`; the game outputs the
validity bit of the forgery.

Specializing `keygen` to `keygen0` / `keygen1` gives the real / uniform-`t` NMA games whose gap
the MLWE hop bounds. The signature scheme is the same `FiatShamirWithAbort (identificationScheme …)`
used by `nma_security`, so `verify` recomputes `Â = ExpandA(pk.ρ)` from the published seed. -/
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

/-- The advantage of the NMA game with key generator `keygen` is its `true`-probability. The hop
lemma below bounds `|nmaAdvantage keygen0 − nmaAdvantage keygen1|`. -/
noncomputable def nmaAdvantage
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (keygen : ProbComp (PublicKey p prims × SecretKey p))
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) : ℝ≥0∞ :=
  Pr[= true | nmaGame p prims hr maxAttempts keygen main]

/-! ### Short-model EUF-NMA game -/

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
inside `StateT QueryCache ProbComp`. Running an oracle computation through this implementation and
projecting away the final cache turns it into a plain `ProbComp`, which is what the MLWE
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

/-- The concrete MLWE problem embedded by ML-DSA key generation, **seed-based**: the public
challenge is the public matrix seed `ρ = (ExpandSeed(seed)).1` for a uniform `seed`, the secret is
`s₁`, and the output is `t`. The matrix is recovered on demand as `Â := ExpandA(ρ)`, so
`noiseless s₁ ρ = ExpandA(ρ) · s₁`; the secret and error/uniform distributions are uniform.

Sampling `ρ` through `ExpandSeed` (rather than uniformly) makes the `ρ` marginal line up *exactly*
with `keygen0` / `keygen1`, so the uniform-branch identity `(H1)` against `keygen1` is a clean
monad-rewriting fact (no distributional assumption: `keygen1` discards the secret, and its `ρ` is
this same `(ExpandSeed seed).1`). What it does **not** reconcile is the *joint* law of `(ρ, s₁, s₂)`
in `keygen0`, where `(s₁, s₂) = ExpandS((ExpandSeed seed).2)` are derived from the *same* seed as
`ρ`, whereas the MLWE problem samples `s₁`/error independently of `ρ`; that joint independence is
the residual honest-sampling gap `(H0)` recorded below and folded into the ROM by the paper.

The matrix never appears as a free challenge: phrasing the MLWE instance over seeds is exactly the
ROM modeling of Dilithium with `ExpandA` a random oracle, and it makes the distinguisher `B` total
(no `ExpandA`-surjectivity assumption). The `nma_security` statement quantifies over an *abstract*
`mlwe` problem; relating that abstract problem to this concrete seed-based one is a deferred
statement-level obligation. -/
noncomputable def mldsaMLWE (p : Params) (prims : Primitives p)
    [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] :
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

When `(ρ, t)` is real, `B` reproduces `nmaGame … keygen0`; when `t` is uniform, it reproduces
`nmaGame … keygen1`. Thus `B`'s distinguishing advantage is exactly the NMA-game gap (the content
of `nma_keyswap_hop`). The seed-based phrasing means `B` needs no matrix-to-seed embedding. -/
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

/-! ### Short-secret MLWE problems and the seed-to-matrix bridge

The idealized short-key model states its Module-LWE assumption over short `(s₁, s₂)`
(`mldsaMLWEShort`, seed-based; `mldsaMatrixMLWE`, uniform-matrix form). The seed-based problem
reduces to the standard matrix form under the `expandAIdealization` XOF assumption
(`advantage_mldsaMLWEShort_le_matrix`), and `distinguisherBShort` is the induced distinguisher
whose advantage the short key-swap hop bounds. -/

/-- **The short-secret Module-LWE problem for ML-DSA** (seed-based form). The public
challenge is the matrix seed `ρ` itself (uniform), the secret `s₁` and the additive
error `s₂` are uniform on the `η`-bounded box (`sampleShortVec`), and the decision
target is `t = ExpandA(ρ) · s₁ + s₂` versus uniform `t`. This is the distribution the
ML-DSA literature states its MLWE assumption over; unlike a uniform-error variant it
is not information-theoretically trivial, since `ExpandA(ρ) · s₁ + s₂` with short
`(s₁, s₂)` is far from uniform. Bridging the seed-based challenge to the standard
uniform-matrix form is `advantage_mldsaMLWEShort_le_matrix`, under the explicit
`expandAIdealization` assumption. -/
noncomputable def mldsaMLWEShort (p : Params) (prims : Primitives p)
    [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] :
    LearningWithErrors.Problem (Bytes 32) (RqVec p.l) (RqVec p.k) where
  sampleChallenge := $ᵗ (Bytes 32)
  sampleSecret := sampleShortVec p.l p.eta
  sampleError := sampleShortVec p.k p.eta
  noiseless := fun s1 rho => prims.expandA rho * s1
  sampleUniform := $ᵗ (RqVec p.k)

/-- **The matrix-based short Module-LWE problem for ML-DSA.** The standard form: the
public challenge is a uniform matrix `A`, the secret and error are uniform on the
`η`-bounded box, and the decision target is `A · s₁ + s₂` versus uniform. This is the
literature-facing hardness assumption; `mldsaMLWEShort` reduces to it under
`expandAIdealization` (`advantage_mldsaMLWEShort_le_matrix`). -/
noncomputable def mldsaMatrixMLWE (p : Params)
    [SampleableType (TqMatrix p.k p.l)]
    [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] :
    LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k) where
  sampleChallenge := $ᵗ (TqMatrix p.k p.l)
  sampleSecret := sampleShortVec p.l p.eta
  sampleError := sampleShortVec p.k p.eta
  noiseless := fun s1 A => A * s1
  sampleUniform := $ᵗ (RqVec p.k)

/-- **ExpandA idealization (quantified XOF-as-random-matrix step).** For every
distinguisher `D` receiving both the seed and the matrix, the pair
`(ρ, ExpandA(ρ))` for uniform `ρ` is `εA`-indistinguishable from `(ρ, A)` with `A`
uniform and independent of `ρ`.

This is the standard random-oracle reading of `ExpandA` (Dilithium's `A = ExpandA(ρ)`
with `ExpandA` modeled as a random function), stated once with inspectable content
rather than supplied per-reduction. For a fixed deterministic `prims.expandA` the
unrestricted-quantifier form is only satisfiable at large `εA` (a distinguisher may
recompute `ExpandA(ρ)` and compare); pending the cost-model infrastructure (#460) it
should be read computationally, against bounded distinguishers, where it is the
assumption that SHAKE-based expansion yields a pseudorandom matrix. -/
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
`(ρ, t)`, run the NMA forging strategy
`main` on `pk`, simulate the random oracle to verify the returned forgery, and output the
validity bit — typed against the short-secret problem `mldsaMLWEShort` and the short-key
scheme `identificationSchemeShort`. When `(ρ, t)` is real it reproduces
`nmaGameShort … keygenShort`; when `t` is uniform it reproduces `nmaGameShort … keygenShort1`
(`nma_keyswap_hop_short`). -/
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

/-- Lift a seed-based short-MLWE adversary to the uniform-matrix problem: run it on a
freshly sampled seed and the challenged target vector, discarding the matrix. -/
noncomputable def matrixLift
    (B : LearningWithErrors.Adversary (mldsaMLWEShort p prims)) :
    LearningWithErrors.Adversary (mldsaMatrixMLWE p) :=
  fun c => do
    let rho ← $ᵗ (Bytes 32)
    B (rho, c.2)

omit [DecidableEq prims.High] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] [IsUniformSpec unifSpec] in
/-- **Seed-to-matrix bridge.** Under `expandAIdealization`, any adversary against the
seed-based short problem yields one against the standard uniform-matrix problem: the
matrix adversary runs the seed adversary on a freshly sampled seed and the challenged
target vector. The uniform branches agree exactly (both present an independent uniform
`t`), and the real branches differ by one application of the idealization at the
distinguisher `D ρ A := s₁ ← S_η^ℓ; s₂ ← S_η^k; B (ρ, A·s₁ + s₂)`.

Proof recipe: rewrite both advantages via `advantage_eq_game_boolDistAdvantage` and
`ProbComp.boolDistAdvantage`; the `game1` branches are identified by stripping the
unused matrix draw (`probOutput_bind_const`, with `Pr[⊥ | $ᵗ _] = 0`) and commuting
the independent uniform draws (`evalDist_bind_bind_swap`); the `game0` branches
are `≤ εA` by `hA` applied at `D` above, after `bind_assoc` normalization. Conclude
by the triangle inequality. -/
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
      evalDist_bind_bind_swap
        ($ᵗ (Bytes 32)) ($ᵗ (RqVec p.k)) (fun rho t => B (rho, t))]
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
        matrixLift, hD,
        bind_assoc, pure_bind]
      -- Commute the trailing `ρ` draw to the front (three independent-draw transpositions).
      rw [probOutput_def, probOutput_def]
      congr 1
      refine Eq.trans (evalDist_bind_congr' _ (fun A => evalDist_bind_congr' _ (fun s1 =>
        evalDist_bind_bind_swap (sampleShortVec p.k p.eta) ($ᵗ (Bytes 32))
          (fun s2 rho => B (rho, A * s1 + s2))))) ?_
      refine Eq.trans (evalDist_bind_congr' _ (fun A =>
        evalDist_bind_bind_swap (sampleShortVec p.l p.eta) ($ᵗ (Bytes 32))
          (fun s1 rho => sampleShortVec p.k p.eta >>= fun s2 => B (rho, A * s1 + s2)))) ?_
      exact evalDist_bind_bind_swap
        ($ᵗ (TqMatrix p.k p.l)) ($ᵗ (Bytes 32))
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
adversary, the MLWE distinguishing advantage is exactly the Boolean distinguishing advantage between
the two single-branch games `game0` (real distribution) and `game1` (uniform distribution).

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
/-- **NMA-game / distinguisher plumbing.** Pushing the `keygen` sampling out of the
Fiat-Shamir-with-aborts runtime: the `Pr[= true]` of `nmaGame … keygen` equals the `Pr[= true]` of
first sampling `(pk, _) ← keygen` (in plain `ProbComp`) and then running the forge-and-verify tail
through `simulateToProbComp` — which is exactly the body of `distinguisherB` evaluated at `pk`.

This is the bundled-semantics fact `runtime.evalDist (liftM oa >>= rest) = 𝒟[oa] >>= …`
(`SPMFSemantics.withStateOracle` interpret/observe with `roSim.run'_liftM_bind`), specialised to
the ML-DSA NMA game; it reduces both (H0) and (H1) to comparing the *key distribution* against
`mldsaMLWE`'s `distr` / `uniformDistr`, with all the runtime plumbing already discharged. -/
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

/-- **The MLWE key-swap hop (Lemma 7, Step 1).** For every NMA forging strategy `main`, the gap
between the real-`t` and uniform-`t` EUF-NMA games is bounded by (in fact equal to) the decisional
MLWE advantage of the seed-based distinguisher `B`.

The proof factors through three facts:
- **(Hadv)** the MLWE advantage equals `(game0 B).boolDistAdvantage (game1 B)`
  (`advantage_eq_game_boolDistAdvantage`, fully proven and generic);
- **(H1)** `nmaGame … keygen1` and `game1 (mldsaMLWE) B` have equal `Pr[= true]`
  (proven below: both are the uniform-`t` game, and the `ρ` marginals coincide because
  `mldsaMLWE` samples `ρ` through the *same* `ExpandSeed` that `keygen1` uses, and `keygen1`'s
  secret is discarded);
- **(H0)** `nmaGame … keygen0` and `game0 (mldsaMLWE) B` have equal `Pr[= true]` — discharged from
  the honest-sampling field `h_laws.expandS_honest_sampling` (the ROM idealization of
  `ExpandSeed`/`ExpandS`); see the inline comment for exactly what it needs.

This is the first of the three steps of `nma_security`; steps 2 and 3 (the `H₁` reprogramming and
the SelfTargetMSIS extraction) are handled elsewhere. The bound is stated on `toReal` because the
NMA advantages are `ℝ≥0∞` while MLWE advantage is `ℝ`. -/
theorem nma_keyswap_hop (h_laws : Primitives.Laws prims nttOps)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    |(nmaAdvantage p prims hr maxAttempts (keygen0 p prims) main).toReal -
        (nmaAdvantage p prims hr maxAttempts (keygen1 p prims) main).toReal| ≤
      LearningWithErrors.advantage (mldsaMLWE p prims)
        (distinguisherB p prims hr maxAttempts main) := by
  set B := distinguisherB p prims hr maxAttempts main (M := M) with hB
  -- (Hadv): the MLWE advantage is exactly the gap between the two single-branch games.
  apply le_of_eq
  rw [advantage_eq_game_boolDistAdvantage (mldsaMLWE p prims) B,
    ProbComp.boolDistAdvantage, nmaAdvantage, nmaAdvantage]
  -- It now suffices to identify `Pr[= true]` of each NMA game with the matching MLWE game.
  -- (H0) real branch and (H1) uniform branch.
  have hH1 : Pr[= true | nmaGame p prims hr maxAttempts (keygen1 p prims) main] =
      Pr[= true | LearningWithErrors.game1 (mldsaMLWE p prims) B] := by
    -- (H1) uniform-branch identity. Both games sample `t` uniformly and discard `keygen1`'s
    -- secret `(s₁, s₂)`; the public key reduces to `⟨(ExpandSeed seed).1, Power2Round(t).1⟩`,
    -- which is exactly what `game1 = uniformDistr >>= B` builds (its challenge `ρ` is sampled
    -- through the *same* `ExpandSeed seed`, see `mldsaMLWE.sampleChallenge`). This is a pure
    -- monad-rewriting identity once `nmaGame`/`liftProbComp` and `simulateToProbComp` are
    -- recognised as the same `withStateOracle` semantics; no distributional assumption.
    rw [nmaGame_eq_keygen_bind]
    simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr, hB, distinguisherB,
      mldsaMLWE, keygen1, keyFromMaterial, bind_assoc, pure_bind]
    rw [probOutput_def, probOutput_def, SPMF.evalDist_def]
  have hH0 : Pr[= true | nmaGame p prims hr maxAttempts (keygen0 p prims) main] =
      Pr[= true | LearningWithErrors.game0 (mldsaMLWE p prims) B] := by
    -- (H0) real-branch identity — THE residual honest-sampling assumption.
    -- `nmaGame … keygen0` samples one `seed ← $ᵗ Bytes 32`, derives `ρ := (ExpandSeed seed).1`,
    -- `(s₁, s₂) := ExpandS (ExpandSeed seed).2`, and sets `t := ExpandA(ρ)·s₁ + s₂`.
    -- `game0 = distr >>= B` instead samples `ρ` through `ExpandSeed` but `s₁ ← $ᵗ RqVec l`,
    -- `s₂ ← $ᵗ RqVec k` *independently* of `ρ` and of each other, with `t := ExpandA(ρ)·s₁ + s₂`.
    -- These agree on `Pr[= true]` iff the joint law of `(ρ, s₁, s₂)` produced by
    -- `ExpandSeed`/`ExpandS` from one uniform `seed` equals the product law
    -- `((ExpandSeed (·)).1 of uniform seed) ⊗ Uniform(RqVec l) ⊗ Uniform(RqVec k)`.
    -- This is the ML-DSA *honest sampling assumption* (`ExpandSeed`/`ExpandS` modeled as
    -- independent uniform samplers in the ROM); it is NOT derivable from the deterministic
    -- `prims` and must enter as an added hypothesis on `prims` (or be supplied by the ROM
    -- modeling of `ExpandSeed`/`ExpandA`). See obligation (1) in the closing note.
    rw [nmaGame_eq_keygen_bind]
    simp only [LearningWithErrors.game0, LearningWithErrors.distr, hB, distinguisherB,
      mldsaMLWE, keygen0, keyFromMaterial, bind_assoc, pure_bind]
    -- After the runtime plumbing the goal is purely about the *key distribution*:
    --   LHS: `seed ← $ᵗ; t := ExpandA((ExpandSeed seed).1)·(ExpandS (ExpandSeed seed).2).1
    --           + (ExpandS (ExpandSeed seed).2).2; run B-tail on pk(seed, t)`
    --   RHS: `seed ← $ᵗ; s₁ ← $ᵗ; s₂ ← $ᵗ; t := ExpandA((ExpandSeed seed).1)·s₁ + s₂;
    --           run B-tail on pk(seed, t)`.
    -- These coincide exactly when `(s₁, s₂) = ExpandS (ExpandSeed seed).2` is, jointly over a
    -- uniform `seed`, distributed as an *independent* `Uniform(RqVec l) × Uniform(RqVec k)`
    -- (and independent of `(ExpandSeed seed).1`). That is the ML-DSA honest-sampling assumption
    -- on `ExpandSeed`/`ExpandS`, not derivable from the deterministic `prims`; see obligation (1).
    exact probOutput_congr rfl (h_laws.expandS_honest_sampling
      (fun rho s1 s2 => simulateToProbComp p prims (M := M) (do
        let d ← main ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2)))
  -- The hop is in fact an *equality* modulo (H0)/(H1): after rewriting both NMA games into the
  -- matching MLWE games the bound becomes `|x - y| = |x - y|`, closed by reflexivity.
  rw [hH0, hH1]

/-! ### The exact short-model key-swap hop -/

omit [SampleableType (RqVec p.k)] in
/-- Short-model NMA-game / distinguisher plumbing: the `nmaGame_eq_keygen_bind` rewrite at the
short scheme. Pushing the `keygen` sampling out of the Fiat-Shamir-with-aborts runtime, the
`Pr[= true]` of `nmaGameShort … keygen` equals that of first sampling `(pk, _) ← keygen` in
plain `ProbComp` and then running the forge-and-verify tail through `simulateToProbComp` —
exactly the body of `distinguisherBShort` evaluated at `pk`. -/
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

/-- **The exact short-model key-swap hop.** Against the idealized key generators
`keygenShort` / `keygenShort1`, the short-model NMA-game gap **is** the `mldsaMLWEShort`
distinguishing advantage of `distinguisherBShort` — both branch identifications are pure
monad-rewriting identities, with no statistical slack: the key generators sample
`ρ`, `K`, `s₁`, `s₂` independently, exactly as the problem's `distr`/`uniformDistr`
do (the unused `K` draw strips off, being the leading draw).

Proof recipe: both branches follow the same shape: `rw [nmaGameShort_eq_keygen_bind]`,
`simp only [LearningWithErrors.game0/1, LearningWithErrors.distr/uniformDistr,
distinguisherBShort, mldsaMLWEShort, keygenShort/1, keyFromMaterial, bind_assoc, pure_bind]`,
strip the leading `K` draw with `probOutput_bind_const` (`Pr[⊥ | $ᵗ (Bytes 32)] = 0`), and
close with `probOutput_def`/`SPMF.evalDist_def`. -/
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
noncomputable def mldsaSTMSIS (M : Type) :
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

omit [DecidableEq M] [SampleableType (CommitHashBytes p)] in
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
`(msg, none)` is mapped to a dummy preimage with a zeroed response, which the STMSIS RO-consistency
check rejects. The matrix in `params.1` is ignored by `C` (it equals `ExpandA(params.2.ρ)`).

The STMSIS experiment then looks up `c̃ = H(msg, w')` in the oracle cache and checks
`mldsaSTMSIS.isValid Â pk c̃ (z, h)`, which recomputes `w'` from `(pk, c̃, (z, h))` and runs the
identification verifier — exactly what the NMA `verify` does after querying `H(msg, w')`. -/
noncomputable def extractorC [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
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
      -- Aborting forgery: no valid preimage. Emit a dummy that fails RO consistency / `isValid`.
      return ((msg, default), default)

/-- **Per-key STMSIS read-back comparison.** For a fixed public key `pk`, the NMA forge-and-verify
tail (run through `simulateToProbComp`) accepts no more often than the SelfTargetMSIS experiment
tail of `extractorC` at the matching parameters `(ExpandA(ρ), pk)`.

Both tails first simulate `main pk` against the same random oracle from the empty cache; the proof
compares them after that shared prefix (`probOutput_bind_mono`). On an aborting forgery the NMA tail
is deterministically `false`. On a forgery `some (w', (z, h))` both branches issue the *same*
`H(msg, w')` query on the *same* cache, so the random answer `c̃` and the resulting cache coincide;
the STMSIS experiment then reads `c̃` back and `mldsaSTMSIS.isValid` recovers `w'` as exactly the
`useHintVec …` value that `verify` checks against, so an accepted NMA forgery is a valid STMSIS
solution. -/
private theorem stmsis_tail_le
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims)))
    (pk : PublicKey p prims) :
    Pr[= true | simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← main pk
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify pk msg σ)] ≤
      Pr[= true | do
        let ((hashInput, response), cache) ←
          (simulateQ (roImpl p prims (M := M))
            ((extractorC p prims main).run (prims.expandA pk.rho, pk))).run ∅
        match cache hashInput with
        | some hashOutput =>
            pure ((mldsaSTMSIS p prims M).isValid (prims.expandA pk.rho) pk hashInput hashOutput
              response)
        | none => pure false] := by
  classical
  -- Decompose both tails over the shared simulation of `main pk` from the empty cache.
  unfold simulateToProbComp extractorC
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
    -- An accepted NMA forgery is a valid STMSIS solution. The self-target binding
    -- `hashInput.2 = w'` holds because the queried preimage is exactly `(msg, w')`, so the binding
    -- reduces to `decide (w' = w') = true`; commitment recoverability is the middle conjunct of
    -- `verify`, which `isValid` discharges by `decide (X = X)`.
    rw [probOutput_pure, probOutput_pure]
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
      rw [if_pos hverify.symm, if_pos hvalid.symm]
    · simp only [Bool.not_eq_true] at hverify
      rw [hverify]
      simp

/-- **The SelfTargetMSIS extraction bound (Lemma 7, Step 3).** The uniform-`t` EUF-NMA advantage is
bounded by the SelfTargetMSIS advantage of the extractor `C`.

A forgery accepted by the NMA game (after the `H(msg, w')` query inside `verify`) is exactly a valid
SelfTargetMSIS solution for `mldsaSTMSIS`: `C` reproduces the forger's oracle trace, the
experiment's RO-consistency lookup recovers the same `c̃ = H(msg, w')`, `isValid` recovers `w'` and
runs the identical verifier. The reduction to the per-key comparison `stmsis_tail_le` is the
bundled-semantics rewrite (`nmaGame_eq_keygen_bind`) plus monotonicity over the shared `keygen1`
prefix; the per-key step then handles the cache read-back and commitment recoverability. -/
theorem nmaAdvantage_keygen1_le_stmsis
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    nmaAdvantage p prims hr maxAttempts (keygen1 p prims) main ≤
      SelfTargetMSIS.advantage (extractorC p prims main) := by
  -- Both `Pr[= true]`s reduce, through the shared `withStateOracle` random-oracle semantics, to:
  --   sample the uniform-`t` key `(pk, _)`; run `main pk` against the RO; on `some (w', (z,h))`
  --   read `c̃ = H(msg, w')` from the cache and accept iff `ids.verify pk w' c̃ (z,h)`.
  -- The NMA game performs exactly this (its `verify` queries `H(msg, w')` then runs `ids.verify`);
  -- the STMSIS experiment performs exactly this (its RO-consistency lookup yields `c̃`, and
  -- `mldsaSTMSIS.isValid` recovers `w'` from `(pk, c̃, (z,h))` and runs `ids.verify`).  After the
  -- bundled-semantics rewrite (`nmaGame_eq_keygen_bind`) both sides bind over the same `keygen1`
  -- prefix, so monotonicity (`probOutput_bind_mono`) reduces to the per-key comparison
  -- `stmsis_tail_le`, which packages the cache read-back and commitment recoverability.
  classical
  rw [nmaAdvantage, nmaGame_eq_keygen_bind, SelfTargetMSIS.advantage,
    SelfTargetMSIS.experiment]
  rw [probOutput_def, SPMF.evalDist_def]
  -- The STMSIS `sampleParams` is exactly `keygen1` followed by publishing `(ExpandA(ρ), pk)`, so
  -- both `Pr[= true]`s bind over the same `keygen1` prefix; compare them per-key.
  change Pr[= true | (keygen1 p prims) >>= _] ≤
    Pr[= true | ((mldsaSTMSIS p prims M).sampleParams) >>= _]
  rw [show (mldsaSTMSIS p prims M).sampleParams =
      (keygen1 p prims) >>= fun pkSk => pure (prims.expandA pkSk.1.rho, pkSk.1) from rfl]
  rw [bind_assoc]
  refine probOutput_bind_mono ?_
  rintro ⟨pk, sk⟩ _
  rw [pure_bind]
  convert stmsis_tail_le p prims hr maxAttempts main pk using 2
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
/-- **NMA Security (Lemma 7, CRYPTO 2023).**

For every EUF-NMA adversary `A` against the ML-DSA scheme (instantiated via `FiatShamirWithAbort`
over the real ML-DSA key generation `keygen0`), there exist an MLWE adversary `B` and a
SelfTargetMSIS adversary `C` such that

  `Adv^{EUF-NMA}(A) ≤ Adv^{MLWE}(B) + Adv^{SelfTargetMSIS}(C)`.

The reductions are the concrete ones built in this file: the MLWE key-swap distinguisher
`distinguisherB` (whose advantage against the seed-based `mldsaMLWE` problem dominates the
real-vs-uniform key gap, `nma_keyswap_hop`) and the SelfTargetMSIS extractor `extractorC` (which
turns a uniform-`t` forgery into a short self-target solution, `nmaAdvantage_keygen1_le_stmsis`).

Because the verifier recomputes `Â = ExpandA(pk.ρ)` from the published seed, the concrete MLWE
instance is phrased over seeds (`mldsaMLWE`, with `Sample = Bytes 32`), whose `Sample` type differs
from an abstract matrix-based `mlwe`. The hypothesis `hMlweBridge` therefore supplies, for every
forging strategy, an abstract MLWE adversary at least as good as `distinguisherB`. The
SelfTargetMSIS side has matching types, so `hStmsis` is a plain equality `stmsis = mldsaSTMSIS p
prims M`, and
`hGen : hr.gen = keygen0 p prims` pins the Fiat-Shamir key generation to the real ML-DSA keygen.

This is the EUF-NMA half (Lemma 7) of the ML-DSA security proof; the CMA-to-NMA statistical step
(`euf_cma_security`) composes on top of it. -/
theorem nma_security (h_laws : Primitives.Laws prims nttOps)
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hStmsis : stmsis = mldsaSTMSIS p prims M)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      ∃ B : LearningWithErrors.Adversary mlwe,
        LearningWithErrors.advantage (mldsaMLWE p prims)
          (distinguisherB p prims hr maxAttempts main) ≤
          LearningWithErrors.advantage mlwe B) :
    ∀ (adv : SignatureAlg.eufNmaAdv
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts)),
    ∃ (mlweReduction : LearningWithErrors.Adversary mlwe)
      (stmsisReduction : SelfTargetMSIS.Adversary stmsis),
      adv.advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal (LearningWithErrors.advantage mlwe mlweReduction) +
        SelfTargetMSIS.advantage stmsisReduction := by
  classical
  intro adv
  obtain ⟨B, hB⟩ := hMlweBridge adv.main
  subst hStmsis
  refine ⟨B, extractorC p prims adv.main, ?_⟩
  -- The EUF-NMA experiment is the real-`t` NMA game with `main := adv.main`.
  have hadv : adv.advantage (FiatShamirWithAbort.runtime
      (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) =
      nmaAdvantage p prims hr maxAttempts (keygen0 p prims) adv.main := by
    rw [SignatureAlg.eufNmaAdv.advantage, nmaAdvantage, nmaGame]
    rw [SignatureAlg.eufNmaExp]
    simp only [FiatShamirWithAbort, hGen]
    rfl
  rw [hadv]
  -- Bound the two NMA games by the MLWE distinguisher and the STMSIS extractor.
  set pc0 := (do
      let (pk, _) ← keygen0 p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← adv.main pk
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpc0
  set pc1 := (do
      let (pk, _) ← keygen1 p prims
      simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← adv.main pk
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          pk msg σ) : ProbComp Bool) with hpc1
  have hg0 : nmaAdvantage p prims hr maxAttempts (keygen0 p prims) adv.main =
      Pr[= true | pc0] := by
    rw [nmaAdvantage, nmaGame_eq_keygen_bind, probOutput_def, probOutput_def, SPMF.evalDist_def]
  have hg1 : nmaAdvantage p prims hr maxAttempts (keygen1 p prims) adv.main =
      Pr[= true | pc1] := by
    rw [nmaAdvantage, nmaGame_eq_keygen_bind, probOutput_def, probOutput_def, SPMF.evalDist_def]
  -- Triangle bound: real game ≤ uniform game + MLWE advantage.
  have htri := ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage pc0 pc1
  rw [hg0]
  refine le_trans htri ?_
  -- `pc0.boolDistAdvantage pc1 = |nmaAdv keygen0 - nmaAdv keygen1| ≤ advantage mldsaMLWE B'`.
  have hbias : pc0.boolDistAdvantage pc1 ≤
      LearningWithErrors.advantage (mldsaMLWE p prims)
        (distinguisherB p prims hr maxAttempts adv.main) := by
    have hk := nma_keyswap_hop p prims h_laws hr maxAttempts (M := M) adv.main
    rw [ProbComp.boolDistAdvantage, ← hg0, ← hg1]
    exact hk
  -- STMSIS extraction bound on the uniform game.
  have hstm := nmaAdvantage_keygen1_le_stmsis p prims hr maxAttempts (M := M) adv.main
  rw [hg1] at hstm
  calc Pr[= true | pc1] + ENNReal.ofReal (pc0.boolDistAdvantage pc1)
      ≤ SelfTargetMSIS.advantage (extractorC p prims adv.main) +
        ENNReal.ofReal (LearningWithErrors.advantage (mldsaMLWE p prims)
          (distinguisherB p prims hr maxAttempts adv.main)) := by
        exact add_le_add hstm (ENNReal.ofReal_le_ofReal hbias)
    _ ≤ ENNReal.ofReal (LearningWithErrors.advantage mlwe B) +
        SelfTargetMSIS.advantage (extractorC p prims adv.main) := by
        rw [add_comm]
        exact add_le_add (ENNReal.ofReal_le_ofReal hB) le_rfl

end Headline

/-! ## Status

**Re-seed-base done.** `MlweEmbedding` is gone: `mldsaMLWE` is now phrased over the public *seed*
`ρ` (sampled through `ExpandSeed`), with the matrix defined on demand as `ExpandA(ρ)`;
`distinguisherB` consumes `(ρ, t)` directly and is total. The whole `nma_security` headline is
proven and axiom-clean (`[propext, Classical.choice, Quot.sound]`), assembled from:

1. **`(Hadv)`/`(H1)`/`(H0)` MLWE key-swap (`nma_keyswap_hop`).** `(Hadv)` and the uniform branch
   `(H1)` are pure runtime-plumbing rewrites (`advantage_eq_game_boolDistAdvantage`,
   `nmaGame_eq_keygen_bind`). The real branch `(H0)` reduces, after the plumbing, to the pure
   key-distribution identity
   `𝒟[seed ← $ᵗ; run B-tail on pk(seed, ExpandA(ρ)·(ExpandS ρ').1 + (ExpandS ρ').2)] =
    𝒟[seed ← $ᵗ; s₁ ← $ᵗ; s₂ ← $ᵗ; run B-tail on pk(seed, ExpandA(ρ)·s₁ + s₂)]`
   (with `ρ = (ExpandSeed seed).1`, `ρ' = (ExpandSeed seed).2`), which is discharged by the
   honest-sampling field `Primitives.Laws.expandS_honest_sampling` carried by `h_laws`: the ROM
   idealization of `ExpandSeed`/`ExpandS` as independent uniform XOFs. (This idealization is a
   modeling assumption, not derivable from the deterministic `prims`; strengthening or instantiating
   it on a concrete `prims` is the one remaining modeling decision.)

2. **STMSIS extraction (`nmaAdvantage_keygen1_le_stmsis`).** Both `Pr[= true]`s reduce, through the
   shared `withStateOracle` semantics, to: sample the uniform-`t` key, run the forger against the
   RO, and on `some (w', (z,h))` read `c̃ = H(msg, w')` from the cache and accept iff
   `ids.verify pk w' c̃ (z,h)`. After `nmaGame_eq_keygen_bind` both sides bind over the same
   `keygen1` prefix, so `probOutput_bind_mono` reduces to the per-key lemma `stmsis_tail_le`, which
   decomposes both tails over the shared `main pk` simulation, gives weight `0` to the aborting
   branch, and on a non-aborting forgery couples the single `H(msg, w')` query — the cached answer
   is read back (`QueryImpl.withCaching_run_some`/`_none`, `QueryCache.cacheQuery_self`) and
   `verify = true → isValid = true` (the middle `decide (X = X)` conjunct) closes the per-answer
   inequality.

3. **Bridge to the abstract `mlwe`/`stmsis`/`hr` of `nma_security`.** `nma_security` quantifies over
   an *abstract* `mlwe`, an *abstract* `stmsis`, and an *abstract* `hr` whose `gen` need not be
   ML-DSA keygen, while the reductions here are against the *concrete* `mldsaMLWE` / `mldsaSTMSIS`
   and `keygen0/1`. The bridge hypotheses are part of the statement: `hGen : hr.gen = keygen0 p
   prims`, `hStmsis : stmsis = mldsaSTMSIS p prims M`, and `hMlweBridge` supplying an abstract MLWE
   adversary at least as good as `distinguisherB`. The proof combines (1) and (2) through the
   triangle bound `probOutput_true_le_add_ofReal_boolDistAdvantage`.
-/

end MLDSA
