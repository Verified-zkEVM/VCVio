/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import LatticeCrypto.MLDSA.Security
import LatticeCrypto.MLDSA.SecurityHVZK
import VCVio.CryptoFoundations.Asymptotics.Negligible
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# ML-DSA EUF-NMA Security: the MLWE key-swap hop (Lemma 7, Step 1)

This file builds the reduction infrastructure for the ML-DSA EUF-NMA security theorem
`MLDSA.nma_security` (issue #227, the real Dilithium Lemma 7), covering the **MLWE key-swap hop**
and the **SelfTargetMSIS extractor**:

1. **MLWE key-swap (`nma_keyswap_hop`).** Replace the honest key generation, where the public key
   vector is `t = Â · s₁ + s₂`, with a variant `keygen1` that samples `t` uniformly. The gap
   between the two EUF-NMA games is bounded by the decisional MLWE advantage of the (seed-based)
   distinguisher `B = distinguisherB`, plus the honest-sampling slack `idealGap`. The `(Hadv)` and
   uniform-branch `(H1)` parts are pure runtime-plumbing rewrites; the real-branch `(H0)` is
   controlled by the `honestSamplingSlack` hypothesis — the quantitative total-variation ROM
   modeling of `ExpandSeed`/`ExpandS`, carried as the real slack `idealGap`.
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

/-- **Honest-sampling slack of the secret derivation (ML-DSA ROM modeling, quantitative form).**

For a real bound `idealGap`, this asserts that for *every* continuation `f`, the real key
derivation (drawing the secrets `(s₁, s₂) = ExpandS((ExpandSeed seed).2.1)` deterministically
from the same uniform `seed` that produces `ρ = (ExpandSeed seed).1`) differs from the ideal
derivation (drawing `s₁`, `s₂` independently and uniformly while keeping the same `ρ`) by total
variation distance at most `idealGap`.

This is the quantitative replacement for the (false-as-equality) honest-sampling idealization:
`ExpandSeed`/`ExpandS` are deterministic XOFs, so the real derivation is a deterministic image of
at most `2^256` seeds and can never *equal* a full-support uniform over the vastly larger secret
space. The honest model carries the residual distance as an explicit real `idealGap` that enters
the security bound additively (and is `0` exactly in the idealized limit). It is satisfiable for
any concrete `prims` — `tvDist` is always at most `1`, so `idealGap = 1` is a trivial witness, and
the genuine ROM-modeling bound supplies the meaningful value. It is consumed only by
`MLDSA.NMA.nma_keyswap_hop` to bound the `(H0)` real-branch residue. -/
def honestSamplingSlack (idealGap : ℝ) : Prop :=
  ∀ {γ : Type}
    [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] [IsUniformSpec unifSpec]
    (f : Bytes 32 → RqVec p.l → RqVec p.k → ProbComp γ),
    tvDist (do
        let seed ← $ᵗ (Bytes 32)
        f (prims.expandSeed seed).1
          (prims.expandS (prims.expandSeed seed).2.1).1
          (prims.expandS (prims.expandSeed seed).2.1).2)
      (do
        let seed ← $ᵗ (Bytes 32)
        let s₁ ← $ᵗ (RqVec p.l)
        let s₂ ← $ᵗ (RqVec p.k)
        f (prims.expandSeed seed).1 s₁ s₂) ≤ idealGap

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
between the real-`t` and uniform-`t` EUF-NMA games is bounded by the decisional MLWE advantage of
the seed-based distinguisher `B`, plus the honest-sampling slack `idealGap`.

The proof factors through three facts:
- **(Hadv)** the MLWE advantage equals `(game0 B).boolDistAdvantage (game1 B)`
  (`advantage_eq_game_boolDistAdvantage`, fully proven and generic);
- **(H1)** `nmaGame … keygen1` and `game1 (mldsaMLWE) B` have equal `Pr[= true]`
  (proven below: both are the uniform-`t` game, and the `ρ` marginals coincide because
  `mldsaMLWE` samples `ρ` through the *same* `ExpandSeed` that `keygen1` uses, and `keygen1`'s
  secret is discarded);
- **(H0)** `nmaGame … keygen0` and `game0 (mldsaMLWE) B` differ in `Pr[= true]` by at most
  `idealGap` — controlled by the honest-sampling slack hypothesis `hSlack` (the quantitative,
  total-variation ROM modeling of `ExpandSeed`/`ExpandS`); see the inline comment for exactly
  what it needs.

The deterministic `ExpandSeed`/`ExpandS` cannot make the real key law *equal* the
independent-uniform secret law (a deterministic image of `2^256` seeds has strictly smaller
support), so `(H0)` is genuinely an inequality with the residual carried by `idealGap`.

This is the first of the three steps of `nma_security`; steps 2 and 3 (the `H₁` reprogramming and
the SelfTargetMSIS extraction) are handled elsewhere. The bound is stated on `toReal` because the
NMA advantages are `ℝ≥0∞` while MLWE advantage and `idealGap` are `ℝ`. -/
theorem nma_keyswap_hop (_h_laws : Primitives.Laws prims nttOps)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (idealGap : ℝ) (_hGap : 0 ≤ idealGap)
    (hSlack : honestSamplingSlack p prims idealGap)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    |(nmaAdvantage p prims hr maxAttempts (keygen0 p prims) main).toReal -
        (nmaAdvantage p prims hr maxAttempts (keygen1 p prims) main).toReal| ≤
      LearningWithErrors.advantage (mldsaMLWE p prims)
        (distinguisherB p prims hr maxAttempts main) + idealGap := by
  set B := distinguisherB p prims hr maxAttempts main (M := M) with hB
  -- (Hadv): the MLWE advantage is exactly the gap between the two single-branch games.
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
  -- (H0) real-branch *bound* — THE residual honest-sampling slack, quantified by `idealGap`.
  -- `nmaGame … keygen0` samples one `seed ← $ᵗ Bytes 32`, derives `ρ := (ExpandSeed seed).1`,
  -- `(s₁, s₂) := ExpandS (ExpandSeed seed).2`, and sets `t := ExpandA(ρ)·s₁ + s₂`.
  -- `game0 = distr >>= B` instead samples `ρ` through `ExpandSeed` but `s₁ ← $ᵗ RqVec l`,
  -- `s₂ ← $ᵗ RqVec k` *independently* of `ρ` and of each other, with `t := ExpandA(ρ)·s₁ + s₂`.
  -- The two `Pr[= true]` differ by at most the total-variation distance of the underlying key
  -- derivations, which `hSlack` bounds by `idealGap`. This is the ML-DSA *honest-sampling slack*
  -- (`ExpandSeed`/`ExpandS` modeled as near-uniform samplers in the ROM); it is NOT derivable from
  -- the deterministic `prims` (deterministic XOFs cannot manufacture entropy beyond their seed) and
  -- enters as a real-number bound, not a false equality. See obligation (1) in the closing note.
  have hH0 : |Pr[= true | nmaGame p prims hr maxAttempts (keygen0 p prims) main].toReal -
      Pr[= true | LearningWithErrors.game0 (mldsaMLWE p prims) B].toReal| ≤ idealGap := by
    rw [nmaGame_eq_keygen_bind]
    simp only [LearningWithErrors.game0, LearningWithErrors.distr, hB, distinguisherB,
      mldsaMLWE, keygen0, keyFromMaterial, bind_assoc, pure_bind]
    -- After the runtime plumbing the goal compares the *key distributions* only:
    --   LHS: `seed ← $ᵗ; t := ExpandA((ExpandSeed seed).1)·(ExpandS (ExpandSeed seed).2).1
    --           + (ExpandS (ExpandSeed seed).2).2; run B-tail on pk(seed, t)`
    --   RHS: `seed ← $ᵗ; s₁ ← $ᵗ; s₂ ← $ᵗ; t := ExpandA((ExpandSeed seed).1)·s₁ + s₂;
    --           run B-tail on pk(seed, t)`.
    -- The `Pr[= true]` gap is at most their TV distance, bounded by `idealGap` via `hSlack`.
    refine le_trans (abs_probOutput_toReal_sub_le_tvDist _ _) ?_
    exact hSlack
      (fun rho s1 s2 => simulateToProbComp p prims (M := M) (do
        let d ← main ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩
        (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts).verify
          ⟨rho, (prims.power2RoundVec (prims.expandA rho * s1 + s2)).1⟩ d.1 d.2))
  -- Assemble: `|a − b| ≤ |a − g₀| + |g₀ − g₁| ≤ idealGap + MLWE`, then reorder.
  rw [hH1]
  refine le_trans (abs_sub_le _
    (Pr[= true | LearningWithErrors.game0 (mldsaMLWE p prims) B].toReal) _) ?_
  rw [add_comm]
  exact add_le_add le_rfl hH0

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
  isValid := fun aHat pk cTilde (z, h) =>
    -- Recover the commitment `w'` from `(pk, c̃, (z, h))` and run the identification verifier.
    let w' := prims.useHintVec h (computeWApprox p prims aHat (prims.sampleInBall cTilde) z pk.t1)
    (identificationScheme p prims).verify pk w' cTilde (z, h)

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
            pure ((mldsaSTMSIS p prims M).isValid (prims.expandA pk.rho) pk hashOutput response)
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
    -- An accepted NMA forgery is a valid STMSIS solution (commitment recoverability is exactly the
    -- middle conjunct of `verify`, which `isValid` discharges by `decide (X = X)`).
    rw [probOutput_pure, probOutput_pure]
    by_cases hverify :
        (identificationScheme p prims).verify pk w' cc.1 (z, h) = true
    · -- Accepted: `isValid` recovers `w'` as the very `useHintVec …` value `verify` checks against,
      -- so its middle conjunct is `decide (X = X) = true` and `isValid = true`.
      have hvalid :
          (mldsaSTMSIS p prims M).isValid (prims.expandA pk.rho) pk cc.1 (z, h) = true := by
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
(`euf_cma_security_of_nma`) composes on top of it. -/
theorem nma_security (h_laws : Primitives.Laws prims nttOps)
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (idealGap : ℝ) (hGap : 0 ≤ idealGap)
    (hSlack : honestSamplingSlack p prims idealGap)
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
        SelfTargetMSIS.advantage stmsisReduction +
        ENNReal.ofReal idealGap := by
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
  -- `pc0.boolDistAdvantage pc1 = |nmaAdv keygen0 - nmaAdv keygen1| ≤ advantage mldsaMLWE B' +
  -- idealGap` (the honest-sampling slack of `nma_keyswap_hop`).
  have hbias : pc0.boolDistAdvantage pc1 ≤
      LearningWithErrors.advantage (mldsaMLWE p prims)
        (distinguisherB p prims hr maxAttempts adv.main) + idealGap := by
    have hk := nma_keyswap_hop p prims h_laws hr maxAttempts idealGap hGap hSlack (M := M) adv.main
    rw [ProbComp.boolDistAdvantage, ← hg0, ← hg1]
    exact hk
  -- `ofReal` of the slacked bound splits additively (both summands are nonnegative).
  have hbias' : ENNReal.ofReal (pc0.boolDistAdvantage pc1) ≤
      ENNReal.ofReal (LearningWithErrors.advantage (mldsaMLWE p prims)
        (distinguisherB p prims hr maxAttempts adv.main)) + ENNReal.ofReal idealGap := by
    refine le_trans (ENNReal.ofReal_le_ofReal hbias) ?_
    exact ENNReal.ofReal_add_le
  -- STMSIS extraction bound on the uniform game.
  have hstm := nmaAdvantage_keygen1_le_stmsis p prims hr maxAttempts (M := M) adv.main
  rw [hg1] at hstm
  calc Pr[= true | pc1] + ENNReal.ofReal (pc0.boolDistAdvantage pc1)
      ≤ SelfTargetMSIS.advantage (extractorC p prims adv.main) +
        (ENNReal.ofReal (LearningWithErrors.advantage (mldsaMLWE p prims)
          (distinguisherB p prims hr maxAttempts adv.main)) + ENNReal.ofReal idealGap) := by
        exact add_le_add hstm hbias'
    _ = (SelfTargetMSIS.advantage (extractorC p prims adv.main) +
        ENNReal.ofReal (LearningWithErrors.advantage (mldsaMLWE p prims)
          (distinguisherB p prims hr maxAttempts adv.main))) + ENNReal.ofReal idealGap := by
        rw [← add_assoc]
    _ ≤ ENNReal.ofReal (LearningWithErrors.advantage mlwe B) +
        SelfTargetMSIS.advantage (extractorC p prims adv.main) +
        ENNReal.ofReal idealGap := by
        refine add_le_add ?_ le_rfl
        rw [add_comm]
        exact add_le_add (ENNReal.ofReal_le_ofReal hB) le_rfl

open scoped Classical in
/-- **EUF-CMA security of ML-DSA (Theorem 4, CRYPTO 2023), wired end to end.**

This is the sound CMA-to-NMA-to-hardness composition. It relocates here (rather than to
`LatticeCrypto.MLDSA.Security`) to avoid the circular import: `nma_security` lives in this
file, which already imports `LatticeCrypto.MLDSA.Security`.

For any EUF-CMA adversary `adv` against the Fiat-Shamir-with-aborts ML-DSA signature, the
advantage is bounded by the MLWE advantage, the SelfTargetMSIS advantage, and the
statistical CMA-to-NMA loss `FiatShamirWithAbort.cmaToNmaLoss`. The proof composes three
pieces:

1. `FiatShamirWithAbort.euf_cma_to_nma`: `adv.advantage ≤ Pr[managedRoNmaExp simulatedNmaAdv]
   + cmaToNmaLoss`, under the good-key/commitment-guessing/abort/query hypotheses;
2. `FiatShamirWithAbort.managedRoNmaExp_simulatedNmaAdv_eq_eufNmaExp` (Option B): the managed-RO
   NMA success probability equals the plain EUF-NMA advantage of `simulatedEufNmaAdv`, the
   cache-forgetting reduction — this is the soundness fix that makes the bridge legitimate;
3. `nma_security` (Lemma 7) applied to `simulatedEufNmaAdv`: `≤ MLWE + SelfTargetMSIS`.

The loss parameters carry the nonnegativity and good-key hypotheses that the abstract
reduction needs; the `nma_security` bridge hypotheses (`hGen`, `hStmsis`, `hMlweBridge`) pin
the abstract hardness problems to the concrete ML-DSA ones. -/
theorem euf_cma_security_of_nma [SampleableType (PublicKey p prims)]
    (h_laws : Primitives.Laws prims nttOps)
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (idealGap : ℝ) (hGap : 0 ≤ idealGap)
    (hSlack : honestSamplingSlack p prims idealGap)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hStmsis : stmsis = mldsaSTMSIS p prims M)
    (sim : PublicKey p prims →
      ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk)
    (hhvzk : (identificationScheme p prims).HVZK sim ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : PublicKey p prims → SecretKey p → Prop)
    (hGood : Pr[ fun xw : PublicKey p prims × SecretKey p => ¬ Good xw.1 xw.2 | hr.gen] ≤
      ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commitment p prims,
      Pr[= cm | Prod.fst <$> (identificationScheme p prims).commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr[= none | (identificationScheme p prims).honestExecution pk sk] ≤
        ENNReal.ofReal p_abort)
    (hAbortSim : ∀ pk sk, Good pk sk →
      Pr[= none | sim pk] ≤ ENNReal.ofReal p_abort)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts))
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims)) (oa := adv.main pk) qS qH)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      ∃ B : LearningWithErrors.Adversary mlwe,
        LearningWithErrors.advantage (mldsaMLWE p prims)
          (distinguisherB p prims hr maxAttempts main) ≤
          LearningWithErrors.advantage mlwe B) :
    ∃ (mlweReduction : LearningWithErrors.Adversary mlwe)
      (stmsisReduction : SelfTargetMSIS.Adversary stmsis),
      adv.advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal (LearningWithErrors.advantage mlwe mlweReduction) +
        SelfTargetMSIS.advantage stmsisReduction +
        ENNReal.ofReal
          (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) +
        ENNReal.ofReal idealGap := by
  classical
  -- Step 1: CMA advantage ≤ managed-RO NMA success of `simulatedNmaAdv` + loss.
  have hcma := FiatShamirWithAbort.euf_cma_to_nma (identificationScheme p prims) hr M
    maxAttempts sim adv ζ_zk hζ hhvzk qS qH ε p_abort δ hε hδ hp₀ hp Good hGood hGuess
    hAbort hAbortSim hQ
  -- Step 2 (Option B bridge): managed-RO NMA success = plain EUF-NMA advantage of the
  -- cache-forgetting reduction `simulatedEufNmaAdv`.
  have hbridge := FiatShamirWithAbort.managedRoNmaExp_simulatedNmaAdv_eq_eufNmaExp
    (identificationScheme p prims) hr M maxAttempts sim adv
  -- Step 3 (Lemma 7): the plain EUF-NMA advantage is bounded by MLWE + SelfTargetMSIS + idealGap.
  obtain ⟨mlweRed, stmsisRed, hnma⟩ := nma_security p prims h_laws mlwe stmsis maxAttempts
    idealGap hGap hSlack hr hGen hStmsis hMlweBridge
    (FiatShamirWithAbort.simulatedEufNmaAdv (identificationScheme p prims) hr M maxAttempts
      sim adv)
  refine ⟨mlweRed, stmsisRed, ?_⟩
  -- Assemble: advantage ≤ (managed = eufNma advantage ≤ MLWE + STMSIS + idealGap) + loss.
  refine le_trans hcma ?_
  have hmanaged : Pr[= true | SignatureAlg.managedRoNmaExp
        (FiatShamirWithAbort.runtime M)
        (FiatShamirWithAbort.simulatedNmaAdv (identificationScheme p prims) hr M maxAttempts
          sim adv)] =
      (FiatShamirWithAbort.simulatedEufNmaAdv (identificationScheme p prims) hr M maxAttempts
        sim adv).advantage (FiatShamirWithAbort.runtime M) := by
    rw [SignatureAlg.eufNmaAdv.advantage, hbridge]
  rw [hmanaged]
  -- `(MLWE + STMSIS + idealGap) + loss = MLWE + STMSIS + loss + idealGap` (commute last two).
  refine le_trans (add_le_add hnma le_rfl) (le_of_eq ?_)
  rw [add_right_comm]

open scoped Classical in
/-- **EUF-CMA security of ML-DSA with the HVZK hypotheses discharged.**

A corollary of `euf_cma_security_of_nma` that instantiates the abstract HVZK simulator with the
proven ML-DSA simulator `hvzkSimulatorReal` and discharges the `hhvzk` obligation via
`idsWithAbort_hvzk_real`. The zero-knowledge slack `ζ_zk` is therefore exposed as its concrete
value `hvzkBoundReal p prims` — the supremum over honestly generated key pairs of the
prover's extra-rejection mass — rather than being a free parameter.

Compared with `euf_cma_security_of_nma`, this statement drops the four HVZK hypotheses
(`sim`, `ζ_zk`, `hζ`, `hhvzk`): the simulator and its quantitative bound are now supplied by the
already-proven `idsWithAbort_hvzk_real`. The remaining hypotheses are unchanged. The abort-rate
side conditions `hAbort`/`hAbortSim` are retained: they bound a different quantity (the abort
probability of, respectively, the honest execution and the simulator) and are not implied by the
HVZK bound without strengthening `p_abort` to `p_abort + ζ_zk`.

The `hvzkBoundReal p prims` slack is a genuine finite real bound (a probability mass projected
through `ENNReal.toReal`, nonnegative by `ENNReal.toReal_nonneg`), not a vacuous `⊤` placeholder. -/
theorem euf_cma_security_of_nma_hvzk [SampleableType (PublicKey p prims)]
    (h_laws : Primitives.Laws prims nttOps)
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (idealGap : ℝ) (hGap : 0 ≤ idealGap)
    (hSlack : honestSamplingSlack p prims idealGap)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPair p prims))
    (hGen : hr.gen = keygen0 p prims)
    (hStmsis : stmsis = mldsaSTMSIS p prims M)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : PublicKey p prims → SecretKey p → Prop)
    (hGood : Pr[ fun xw : PublicKey p prims × SecretKey p => ¬ Good xw.1 xw.2 | hr.gen] ≤
      ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commitment p prims,
      Pr[= cm | Prod.fst <$> (identificationScheme p prims).commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr[= none | (identificationScheme p prims).honestExecution pk sk] ≤
        ENNReal.ofReal p_abort)
    (hAbortSim : ∀ pk sk, Good pk sk →
      Pr[= none | hvzkSimulatorReal p prims pk] ≤ ENNReal.ofReal p_abort)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts))
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims)) (oa := adv.main pk) qS qH)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      ∃ B : LearningWithErrors.Adversary mlwe,
        LearningWithErrors.advantage (mldsaMLWE p prims)
          (distinguisherB p prims hr maxAttempts main) ≤
          LearningWithErrors.advantage mlwe B) :
    ∃ (mlweReduction : LearningWithErrors.Adversary mlwe)
      (stmsisReduction : SelfTargetMSIS.Adversary stmsis),
      adv.advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal (LearningWithErrors.advantage mlwe mlweReduction) +
        SelfTargetMSIS.advantage stmsisReduction +
        ENNReal.ofReal
          (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort
            (hvzkBoundReal p prims) δ hp) +
        ENNReal.ofReal idealGap :=
  euf_cma_security_of_nma p prims h_laws mlwe stmsis maxAttempts idealGap hGap hSlack hr
    hGen hStmsis (hvzkSimulatorReal p prims) (hvzkBoundReal p prims) ENNReal.toReal_nonneg
    (idsWithAbort_hvzk_real p prims h_laws) qS qH ε p_abort δ hε hδ hp₀ hp Good hGood hGuess
    hAbort hAbortSim adv hQ hMlweBridge

/-! ## Asymptotic (negligible) EUF-CMA headline

The non-degenerate asymptotic statement. The scheme is indexed by a security parameter `n`
through a *family* `(p n, prims n)` of ML-DSA parameter/primitive instances, so that the
commitment guessing probability `ε n`, the key-regularity failure `δ n`, and the HVZK slack
`hvzkBoundReal (p n) (prims n)` all shrink (negligibly) as `n → ∞` while the signing / hashing
query budgets `qS n`, `qH n` grow only polynomially in `n`. Under negligible MLWE and
SelfTargetMSIS advantage families this makes the EUF-CMA advantage family negligible.

The earlier fixed-scheme wrapper was degenerate: with a *constant* `ε > 0` the loss term
`2·qS·(qH+1)·ε/(1−p)` is only negligible when the query budgets vanish. Here the slacks are
themselves negligible families, so each loss term is `poly(n) · negligible(n)`, which is negligible
by `negligible_polynomial_mul`. -/

omit nttOps in
/-- A geometric family `r ^ n` with `0 ≤ r < 1` is negligible (after `ENNReal.ofReal`): for every
power `k`, `n ^ k · r ^ n → 0` (`tendsto_pow_const_mul_const_pow_of_lt_one`), and `ENNReal.ofReal`
is continuous. This provides concrete negligible slack/advantage families for the non-vacuity
witness `euf_cma_security_asymptotic_real_satisfiable`. -/
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
  change ENNReal.ofReal
      (FiatShamirWithAbort.cmaToNmaLoss (qS n) (qH n) (ε n) p_abort (ζ_zk n) (δ n) hp) ≤ _
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
/-- **Asymptotic (negligible) EUF-CMA security of ML-DSA.**

The security-parameter-indexed, non-degenerate headline. The ML-DSA scheme is given as a *family*
`(p n, prims n)` over the security parameter `n`, with all carrier instances supplied per `n`. The
hypotheses are the `n`-indexed lifts of those of `euf_cma_security_of_nma_hvzk`, plus:

* polynomial query bounds `qS n ≤ pS.eval n`, `qH n ≤ pH.eval n` (poly-time adversaries);
* negligible commitment-guessing slack `ε`, key-regularity slack `δ`, and HVZK slack
  `hvzkBoundReal (p n) (prims n)` (the commitment / response spaces grow with `n`);
* negligible MLWE and SelfTargetMSIS advantage families `mlweAdv`, `stmsisAdv` dominating every
  reduction adversary (the hardness assumptions, carried as `n`-indexed families per the standard
  ROM model).

The conclusion is that the EUF-CMA advantage family of `adv` is negligible. The proof instantiates
the per-`n` bound `euf_cma_security_of_nma_hvzk`, dominates the two existential reductions by their
negligible families, and bounds the statistical loss family with `cmaToNmaLoss_negligible`: with
polynomially-bounded queries and negligible slacks each loss term is `poly(n) · negligible(n)`.

This is non-vacuous in the real regime: the hypotheses are jointly satisfiable with query budgets
growing polynomially (e.g. `qS n = qH n = n`) and slacks vanishing super-polynomially (e.g.
`ε n = δ n = (1 / 2) ^ n`), which is exactly the standard asymptotic ML-DSA setting — not the
degenerate vanishing-query regime. -/
theorem euf_cma_security_asymptotic_real
    (p' : ℕ → Params) (prims' : ∀ n, Primitives (p' n)) [nttOps' : NTTRingOps]
    (instHigh : ∀ n, DecidableEq (prims' n).High)
    {M' : Type} [DecidableEq M']
    (instCommEq : ∀ n, DecidableEq (Commitment (p' n) (prims' n)))
    (instCommInh : ∀ n, Inhabited (Commitment (p' n) (prims' n)))
    (instRespInh : ∀ n, Inhabited (Response (p' n) (prims' n)))
    (instRql : ∀ n, SampleableType (RqVec (p' n).l))
    (instRqk : ∀ n, SampleableType (RqVec (p' n).k))
    (instChal : ∀ n, SampleableType (CommitHashBytes (p' n)))
    (instPk : ∀ n, SampleableType (PublicKey (p' n) (prims' n)))
    (h_laws : ∀ n, Primitives.Laws (prims' n) nttOps')
    (mlwe : ∀ n, LearningWithErrors.Problem (TqMatrix (p' n).k (p' n).l)
      (RqVec (p' n).l) (RqVec (p' n).k))
    (stmsis : ∀ n, SelfTargetMSIS.Problem
      (TqMatrix (p' n).k (p' n).l) (Response (p' n) (prims' n))
      (PublicKey (p' n) (prims' n)) (M' × Commitment (p' n) (prims' n)) (CommitHashBytes (p' n)))
    (maxAttempts : ℕ → ℕ)
    (hr : ∀ n, GenerableRelation (PublicKey (p' n) (prims' n)) (SecretKey (p' n))
      (validKeyPair (p' n) (prims' n)))
    (hGen : ∀ n, (hr n).gen = keygen0 (p' n) (prims' n))
    (hStmsis : ∀ n, stmsis n = mldsaSTMSIS (p' n) (prims' n) M')
    (qS qH : ℕ → ℕ) (ε δ : ℕ → ℝ) (p_abort : ℝ)
    (hp : p_abort < 1) (hp₀ : 0 ≤ p_abort)
    (hε : ∀ n, 0 ≤ ε n) (hδ : ∀ n, 0 ≤ δ n)
    (Good : ∀ n, PublicKey (p' n) (prims' n) → SecretKey (p' n) → Prop)
    (hGood : ∀ n, Pr[ fun xw : PublicKey (p' n) (prims' n) × SecretKey (p' n) =>
        ¬ Good n xw.1 xw.2 | (hr n).gen] ≤ ENNReal.ofReal (δ n))
    (hGuess : ∀ n, ∀ pk sk, Good n pk sk → ∀ cm : Commitment (p' n) (prims' n),
      Pr[= cm | Prod.fst <$> (identificationScheme (p' n) (prims' n)).commit pk sk] ≤
        ENNReal.ofReal (ε n))
    (hAbort : ∀ n, ∀ pk sk, Good n pk sk →
      Pr[= none | (identificationScheme (p' n) (prims' n)).honestExecution pk sk] ≤
        ENNReal.ofReal p_abort)
    (hAbortSim : ∀ n, ∀ pk sk, Good n pk sk →
      Pr[= none | hvzkSimulatorReal (p' n) (prims' n) pk] ≤ ENNReal.ofReal p_abort)
    (adv : ∀ n, SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort (identificationScheme (p' n) (prims' n)) (hr n) M' (maxAttempts n)))
    (hQ : ∀ n, ∀ pk, FiatShamir.signHashQueryBound M'
      (S' := Option (Commitment (p' n) (prims' n) × Response (p' n) (prims' n)))
      (oa := (adv n).main pk) (qS n) (qH n))
    (hMlweBridge : ∀ n, ∀ (main : PublicKey (p' n) (prims' n) →
        OracleComp (unifSpec + (M' × Commitment (p' n) (prims' n) →ₒ CommitHashBytes (p' n)))
          (M' × Option (Commitment (p' n) (prims' n) × Response (p' n) (prims' n)))),
      ∃ B : LearningWithErrors.Adversary (mlwe n),
        LearningWithErrors.advantage (mldsaMLWE (p' n) (prims' n))
          (distinguisherB (p' n) (prims' n) (hr n) (maxAttempts n) main) ≤
          LearningWithErrors.advantage (mlwe n) B)
    (pS pH : Polynomial ℕ)
    (hqS : ∀ n, qS n ≤ pS.eval n) (hqH : ∀ n, qH n ≤ pH.eval n)
    (mlweAdv stmsisAdv : ℕ → ℝ≥0∞)
    (hmlweNegl : negligible mlweAdv) (hstmsisNegl : negligible stmsisAdv)
    (hMlweBound : ∀ n (B : LearningWithErrors.Adversary (mlwe n)),
      ENNReal.ofReal (LearningWithErrors.advantage (mlwe n) B) ≤ mlweAdv n)
    (hStmsisBound : ∀ n (C : SelfTargetMSIS.Adversary (stmsis n)),
      SelfTargetMSIS.advantage C ≤ stmsisAdv n)
    (idealGap : ℕ → ℝ) (hGap : ∀ n, 0 ≤ idealGap n)
    (hSlack : ∀ n, honestSamplingSlack (p' n) (prims' n) (idealGap n))
    (hGapNegl : negligible (fun n => ENNReal.ofReal (idealGap n)))
    (hεneg : negligible (fun n => ENNReal.ofReal (ε n)))
    (hδneg : negligible (fun n => ENNReal.ofReal (δ n)))
    (hζneg : negligible (fun n => ENNReal.ofReal (hvzkBoundReal (p' n) (prims' n)))) :
    negligible (fun n => (adv n).advantage
      (FiatShamirWithAbort.runtime
        (Commit := Commitment (p' n) (prims' n)) (Chal := CommitHashBytes (p' n)) M')) := by
  have hbound : ∀ n, (adv n).advantage
      (FiatShamirWithAbort.runtime
        (Commit := Commitment (p' n) (prims' n)) (Chal := CommitHashBytes (p' n)) M') ≤
      mlweAdv n + stmsisAdv n +
      ENNReal.ofReal (FiatShamirWithAbort.cmaToNmaLoss (qS n) (qH n) (ε n) p_abort
        (hvzkBoundReal (p' n) (prims' n)) (δ n) hp) +
      ENNReal.ofReal (idealGap n) := by
    intro n
    obtain ⟨mlweRed, stmsisRed, hb⟩ :=
      @euf_cma_security_of_nma_hvzk (p' n) (prims' n) nttOps' (instHigh n) M' _
        (instCommEq n) (instCommInh n) (instRespInh n) (instRql n) (instRqk n)
        (instChal n) (instPk n)
        (h_laws n) (mlwe n) (stmsis n) (maxAttempts n) (idealGap n) (hGap n) (hSlack n)
        (hr n) (hGen n) (hStmsis n)
        (qS n) (qH n) (ε n) p_abort (δ n) (hε n) (hδ n) hp₀ hp (Good n) (hGood n) (hGuess n)
        (hAbort n) (hAbortSim n) (adv n) (hQ n) (hMlweBridge n)
    refine le_trans hb ?_
    gcongr
    · exact hMlweBound n mlweRed
    · exact hStmsisBound n stmsisRed
  refine negligible_of_le hbound ?_
  refine negligible_add (negligible_add (negligible_add hmlweNegl hstmsisNegl) ?_) hGapNegl
  exact cmaToNmaLoss_negligible qS qH ε (fun n => hvzkBoundReal (p' n) (prims' n)) δ p_abort hp
    pS pH hqS hqH hεneg hζneg hδneg

omit nttOps in
/-- **Non-vacuity witness for the asymptotic regime.**

The quantitative hypotheses of `euf_cma_security_asymptotic_real` — *polynomially-bounded* query
budgets together with *negligible* statistical slacks (commitment guessing `ε`, HVZK `ζ_zk`, key
regularity `δ`) and negligible hardness advantage families — are jointly satisfiable with query
budgets that genuinely **grow** with the security parameter. Concretely, taking
`qS n = qH n = n` (bounded by `Polynomial.X`, i.e. *not* vanishing), all slacks and advantage
families equal to `(1 / 2) ^ n`, and `p_abort = 1 / 2`, the resulting `cmaToNmaLoss` family,
together with the two hardness families, is negligible — so the dominating sum in the headline's
internal bound is negligible.

This rules out the degenerate reading of the headline (where polynomial queries against a *fixed*
positive `ε` would force the budgets to vanish): here the budgets grow polynomially while the loss
still decays, which is exactly the standard asymptotic ML-DSA setting. -/
theorem euf_cma_security_asymptotic_real_satisfiable :
    ∃ (qS qH : ℕ → ℕ) (ε ζ_zk δ idealGap : ℕ → ℝ) (p_abort : ℝ) (hp : p_abort < 1)
      (pS pH : Polynomial ℕ) (mlweAdv stmsisAdv : ℕ → ℝ≥0∞),
      (∀ n, qS n ≤ pS.eval n) ∧ (∀ n, qH n ≤ pH.eval n) ∧
      -- the queries genuinely grow (are not the degenerate vanishing-query regime)
      (∀ n, qS n = n) ∧ (∀ n, qH n = n) ∧
      negligible mlweAdv ∧ negligible stmsisAdv ∧
      negligible (fun n => ENNReal.ofReal (ε n)) ∧
      negligible (fun n => ENNReal.ofReal (ζ_zk n)) ∧
      negligible (fun n => ENNReal.ofReal (δ n)) ∧
      negligible (fun n => ENNReal.ofReal (idealGap n)) ∧
      negligible (fun n => mlweAdv n + stmsisAdv n +
        ENNReal.ofReal (FiatShamirWithAbort.cmaToNmaLoss (qS n) (qH n) (ε n) p_abort
          (ζ_zk n) (δ n) hp) +
        ENNReal.ofReal (idealGap n)) := by
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
    hnegE, hnegE, hneg, hneg, hneg, hneg, ?_⟩
  refine negligible_add (negligible_add (negligible_add hnegE hnegE) ?_) hneg
  exact cmaToNmaLoss_negligible (fun n => n) (fun n => n) (fun n => (1 / 2) ^ n)
    (fun n => (1 / 2) ^ n) (fun n => (1 / 2) ^ n) (1 / 2) (by norm_num) Polynomial.X Polynomial.X
    hgrow hgrow hneg hneg hneg

end Headline

/-! ## Status

**Re-seed-base done.** `MlweEmbedding` is gone: `mldsaMLWE` is now phrased over the public *seed*
`ρ` (sampled through `ExpandSeed`), with the matrix defined on demand as `ExpandA(ρ)`;
`distinguisherB` consumes `(ρ, t)` directly and is total. The whole `nma_security` headline is
proven and axiom-clean (`[propext, Classical.choice, Quot.sound]`), assembled from:

1. **`(Hadv)`/`(H1)`/`(H0)` MLWE key-swap (`nma_keyswap_hop`).** `(Hadv)` and the uniform branch
   `(H1)` are pure runtime-plumbing rewrites (`advantage_eq_game_boolDistAdvantage`,
   `nmaGame_eq_keygen_bind`). The real branch `(H0)` reduces, after the plumbing, to comparing the
   key distributions
   `𝒟[seed ← $ᵗ; run B-tail on pk(seed, ExpandA(ρ)·(ExpandS ρ').1 + (ExpandS ρ').2)]` against
   `𝒟[seed ← $ᵗ; s₁ ← $ᵗ; s₂ ← $ᵗ; run B-tail on pk(seed, ExpandA(ρ)·s₁ + s₂)]`
   (with `ρ = (ExpandSeed seed).1`, `ρ' = (ExpandSeed seed).2`). Because `ExpandSeed`/`ExpandS` are
   deterministic, the first is a deterministic image of at most `2^256` seeds and can never *equal*
   the full-support independent-uniform secret law of the second. The residual is therefore carried
   as the explicit total-variation slack `idealGap` supplied by the `honestSamplingSlack` hypothesis
   `hSlack`: the `(H0)` `Pr[= true]` gap is at most `idealGap` (via
   `abs_probOutput_toReal_sub_le_tvDist` plus `hSlack`), and `idealGap` propagates additively into
   the final bound. (This slack is a
   modeling assumption on the XOFs, not derivable from the deterministic `prims`; supplying a
   concrete quantitative bound on a concrete `prims` is the one remaining modeling decision.)

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
