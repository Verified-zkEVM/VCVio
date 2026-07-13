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
# ML-DSA EUF-NMA Security: the short-key MLWE reduction (Lemma 7)

This file builds the reduction infrastructure for the ML-DSA EUF-NMA security theorem
`MLDSA.nma_security_short` (issues #227/#228, the real Dilithium Lemma 7) over the idealized
short-secret key generation `keygenShort`, together with its transfer to the FIPS
seed-derived key generation `keygen0`:

1. **MLWE key-swap (`nma_keyswap_hop_short`).** Replace the honest short-key generation,
   where the public key vector is `t = Â · s₁ + s₂` with `(s₁, s₂)` uniform on the
   `η`-bounded box, by the variant `keygenShort1` that samples `t` uniformly. The gap
   between the two EUF-NMA games **is** the decisional `mldsaMLWEShort` advantage of the
   induced distinguisher `distinguisherBShort`: both branch identifications are exact monad
   identities, so no statistical slack appears.
2. **SelfTargetMSIS extraction (`nmaAdvantage_keygenShort1_le_stmsis`).** Once `t` is
   uniform the key carries no secret, so a forgery is a short vector satisfying the
   SelfTargetMSIS relation; the extractor `extractorCShort` reads `(z, c̃)` out of the
   forged signature. The shared random-oracle simulation lines up the NMA `verify` query
   with the extractor's RO read-back (`stmsis_tail_le_short`), and an accepted forgery is a
   valid SelfTargetMSIS solution by commitment recoverability.
3. **FIPS transfer (`nma_security_fips`).** The deterministic seed-expanded FIPS key
   generator `keygen0` is related to `keygenShort` by the named XOF-replacement assumption
   `expandSReplacement`, so the short-model bound transfers to the FIPS key generation at an
   additive `εPRG`.

The `H₁` reprogramming step of the paper folds into the random-oracle modeling and is not
separated out here. `MLDSA.nma_security_short` assembles steps 1 and 2 under the bridge
hypotheses negotiated in its statement (`hGen`, `hStmsis`, `hMlweBridge`), and
`MLDSA.euf_cma_security_of_nma_short` composes the CMA-to-NMA statistical step on top.

**Algebraic content of the tailored SelfTargetMSIS problem.** `mldsaSTMSISShort.isValid` is
defined through the identification verifier plus the self-target binding;
`stmsisAlgebraicSolution` and the bridge `mldsaSTMSISShort_isValid_iff` re-express an
accepted solution `(z, h)` explicitly as the norm gates `‖z‖∞ < γ₁ − β` and
`weight(h) ≤ ω`, a commitment recovered from the hint as
`w' = UseHint(h, Â·z − SampleInBall(c̃)·(t₁·2^d))` over `R_q`
(`computeWApprox_eq_mul_sub_smul`), and the **binding** of `w'` to the commitment component
of the hash preimage that produced `c̃`, whose RO consistency is enforced by the surrounding
`SelfTargetMSIS.experiment`. At the matched parameters `Â = ExpandA(ρ)` published by
`sampleParams`, acceptance is exactly the norm gates plus the binding
(`mldsaSTMSISShort_isValid_expandA_iff`): a winning solution must have committed — inside
the RO preimage — to the very commitment its response recomputes, before the oracle
answered `c̃` on that preimage. This is the self-target relation an accepted NMA forgery
carries — `w₁ = UseHint(h, ExpandA(ρ)·z − c·(t₁·2^d))` while `c̃ = H(msg, w₁)`
(`identificationSchemeShort_verify_eq_true_iff` plus the cache read-back inside the
extraction proof). The tailored problem still differs from the literature SelfTargetMSIS
normal form in two respects: the linear map is presented through the verifier's
`UseHint`/`Power2Round` compression rather than as the concatenated matrix `[A | I]` acting
on one short vector, and the challenge polynomial `c = SampleInBall(c̃)` is not extracted as
a coefficient block of the solution vector.

## Scope: an idealized proof-level ML-DSA model

The theorems in this file (and the EUF-CMA composition built on them) are about the
**proof-level** scheme `FiatShamirWithAbort (identificationSchemeShort p prims)`, not the
FIPS 204 signing/encoding path. The idealizations, explicitly:

- Signatures are the identification-scheme transcripts `(commitment, challenge hash,
  response)`; the FIPS byte-level encodings, hints, and the `Signature.lean` packing layer
  are not part of the statement.
- The headline key generation is the idealized `keygenShort` — `ρ`, `K` uniform and
  `(s₁, s₂)` uniform on the `η`-bounded box, the distribution the ML-DSA Module-LWE
  assumption is stated over. The deterministic FIPS derivation `keygen0` is covered by the
  corollary `nma_security_fips` under the explicit computational assumption
  `expandSReplacement`.
- The hardness problems are stated over the seed-based key embedding (`mldsaMLWEShort`,
  `mldsaSTMSISShort`); bridging to the standard matrix-based MLWE problem is carried by the
  `hMlweBridge` hypothesis, with the canonical discharge landing on `mldsaMatrixMLWE` via
  `advantage_mldsaMLWEShort_le_matrix` under `expandAIdealization`. The SelfTargetMSIS side
  is characterized algebraically in-file (`stmsisAlgebraicSolution`,
  `mldsaSTMSISShort_isValid_iff`) and carries the genuine self-target binding, in the
  tailored presentation described in the dedicated paragraph above.
- No cost model is attached: the reductions are constructed explicitly but their polynomial
  runtime is not machine-checked, and asymptotic statements quantify over unrestricted
  adversaries — they are not statements about poly-time adversaries.

## What is defined here

The idealized ML-DSA key distribution embeds an MLWE instance: sample a public seed `ρ` and
a signing key `K`, set the public matrix `Â = ExpandA(ρ)`, sample short secrets `(s₁, s₂)`
uniformly on the `η`-bounded box, and publish the `Power2Round` high half of
`t = Â · s₁ + s₂`. The uniform-`t` variant replaces `Â · s₁ + s₂` by a uniform sample. We
package both as `ProbComp` key generators, lift each to an EUF-NMA game over an arbitrary
forging adversary `main`, and exhibit the MLWE distinguisher that interpolates between them:
it reconstructs the public key from the challenge `(ρ, t)` and runs the adversary.

## Modeling note (seeds, not matrices)

The verifier recomputes `Â = ExpandA(pk.ρ)` from the seed stored in the public key, so the
MLWE challenge matrix `Â` must be presented to the adversary *through* a seed `ρ`. Rather
than carrying an embedding witness `ExpandA(ρ) = Â` (which need not exist, since `ExpandA`
is not surjective), we **seed-base** the MLWE problem: the public challenge of
`mldsaMLWEShort` is the *seed* `ρ` itself, and the matrix is *defined* as `Â := ExpandA(ρ)`
wherever it is used, so that `noiseless s₁ ρ = ExpandA(ρ)·s₁`. This is the standard ROM
modeling of Dilithium with `ExpandA` a random oracle, and it makes the distinguisher total:
it consumes `(ρ, t)` and forms `pk = (ρ, Power2Round(t).1)` directly with no embedding. The
seed-based problem reduces to the standard uniform-matrix `mldsaMatrixMLWE` under the
explicit `expandAIdealization` assumption (`advantage_mldsaMLWEShort_le_matrix`).
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
slack), and the deterministic-XOF derivation enters only through the separate
`expandSReplacement` assumption consumed by the FIPS-keygen corollary. -/

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
model; the deterministic seed-expanded `keygen0` is related to it by the
`expandSReplacement` assumption. -/
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

omit [DecidableEq prims.High] [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)] in
/-- **Satisfiability certificate for the FIPS-keygen `hGen` hypothesis.** Some generable
relation over `validKeyPair` has the seed-derived FIPS key generator `keygen0` as its
generator — witnessed by `hrFips`. The FIPS-keygen security corollary hypothesizes such a
relation via `hGen : hr.gen = keygen0 p prims`; this theorem records that the hypothesis
pair `(hr, hGen)` is inhabited, so that statement has non-vacuous instances. -/
theorem keygen0_generable :
    ∃ hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims),
      hr.gen = keygen0 p prims :=
  ⟨hrFips p prims, rfl⟩

/-- **XOF replacement for the ML-DSA secret derivation (`ExpandSeed`/`ExpandS`), quantified
form.** For a real bound `εPRG`, this asserts that no distinguisher receiving
`(ρ, K, s₁, s₂)` can tell the FIPS derivation — expand a uniform 32-byte seed into
`(ρ, ρ', K)` and derive `(s₁, s₂) = ExpandS(ρ')` — from independent sampling with the
correct short marginals: `ρ`, `K` uniform and `(s₁, s₂)` uniform on the `η`-bounded box
`S_η^ℓ × S_η^k`, i.e. exactly the draws of the idealized key generator `keygenShort`.

This is the standard PRG/XOF-replacement reading of `ExpandSeed`/`ExpandS` against the
short-secret marginal: the ideal branch is the box distribution the Module-LWE assumption
for ML-DSA is stated over, so the assumption carries exactly the "SHAKE output is
pseudorandom with the FIPS marginals" step and nothing else. For a fixed deterministic
`prims` the unrestricted-quantifier form is only satisfiable at large `εPRG` — an unbounded
distinguisher can test membership in the `2^256`-point image of the seed expansion — so,
pending the cost-model infrastructure (#460), it should be read computationally, against
bounded distinguishers, where it is the assumption that the SHAKE-derived `(ρ, K, s₁, s₂)`
is pseudorandom with the FIPS marginals. It is consumed by the FIPS-keygen corollary
`nma_security_fips` to transfer the short-model bound to `keygen0`. -/
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
  ∀ D : Bytes 32 → TqMatrix p.k p.l → ProbComp Bool,
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
  [SampleableType (CommitHashBytes p)] in
/-- **Seed-to-matrix bridge.** Under `expandAIdealization`, any adversary against the
seed-based short problem yields one against the standard uniform-matrix problem: the
matrix adversary runs the seed adversary on a freshly sampled seed and the challenged
target vector. The uniform branches agree exactly (both present an independent uniform
`t`), and the real branches differ by one application of the idealization at the
distinguisher `D ρ A := s₁ ← S_η^ℓ; s₂ ← S_η^k; B (ρ, A·s₁ + s₂)`.

Proof recipe: rewrite both advantages via `advantage_eq_game_boolDistAdvantage` and
`ProbComp.boolDistAdvantage`; the `game1` branches are identified by stripping the
unused matrix draw (`probOutput_bind_const`, with `Pr[⊥ | $ᵗ _] = 0`) and commuting
the independent uniform draws (`evalDist_bind_comm_probComp`); the `game0` branches
are `≤ εA` by `hA` applied at `D` above, after `bind_assoc` normalization. Conclude
by the triangle inequality. -/
lemma advantage_mldsaMLWEShort_le_matrix {εA : ℝ}
    (hA : expandAIdealization p prims εA)
    (B : LearningWithErrors.Adversary (mldsaMLWEShort p prims)) :
    LearningWithErrors.advantage (mldsaMLWEShort p prims) B ≤
      LearningWithErrors.advantage (mldsaMatrixMLWE p) (matrixLift p prims B) + εA := by
  -- The goal's games/advantages carry the canonical global `IsUniformSpec unifSpec` instance, but
  -- `hA` (through `expandAIdealization`) carries the section variable `iu`. Name `iu`, then shadow
  -- with the global term so the auxiliary `have`s and the goal share instances; the single residual
  -- `iu`-vs-global gap (only `hA`) is closed inside `h0` via `hips` (both give uniform `toPMF`).
  rename_i iu
  letI : IsUniformSpec unifSpec := instIsUniformSpecNatUnifSpec
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
      FiatShamirWithAbort.evalDist_bind_comm_probComp
        ($ᵗ (Bytes 32)) ($ᵗ (RqVec p.k)) (fun rho t => B (rho, t))]
  have h0 : |(Pr[= true | LearningWithErrors.game0 (mldsaMLWEShort p prims) B]).toReal -
      (Pr[= true | LearningWithErrors.game0 (mldsaMatrixMLWE p) Bm]).toReal| ≤ εA := by
    -- `hA` carries the section instance `iu`; the goal carries the global one (`this`). Both are
    -- `IsUniformSpec unifSpec`, hence share the uniform `toPMF`, so their `IsProbabilitySpec`
    -- projections coincide and the `probOutput`s agree.
    have ext_ips : ∀ (a b : IsProbabilitySpec unifSpec), a.toPMF = b.toPMF → a = b := by
      intro a b h; cases a; cases b; congr
    have hips : (this : IsUniformSpec unifSpec).toIsProbabilitySpec = iu.toIsProbabilitySpec := by
      apply ext_ips
      funext t
      rw [(this : IsUniformSpec unifSpec).toPMF_eq_uniform t, iu.toPMF_eq_uniform t]
      congr 1
      exact Subsingleton.elim _ _
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
        FiatShamirWithAbort.evalDist_bind_comm_probComp (sampleShortVec p.k p.eta) ($ᵗ (Bytes 32))
          (fun s2 rho => B (rho, A * s1 + s2))))) ?_
      refine Eq.trans (evalDist_bind_congr' _ (fun A =>
        FiatShamirWithAbort.evalDist_bind_comm_probComp (sampleShortVec p.l p.eta) ($ᵗ (Bytes 32))
          (fun s1 rho => sampleShortVec p.k p.eta >>= fun s2 => B (rho, A * s1 + s2)))) ?_
      exact FiatShamirWithAbort.evalDist_bind_comm_probComp
        ($ᵗ (TqMatrix p.k p.l)) ($ᵗ (Bytes 32))
        (fun A rho => sampleShortVec p.l p.eta >>= fun s1 =>
          sampleShortVec p.k p.eta >>= fun s2 => B (rho, A * s1 + s2))
    rw [hreal, hunif, hips]
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
/-- **NMA-game plumbing.** Pushing the `keygen` sampling out of the
Fiat-Shamir-with-aborts runtime: the `Pr[= true]` of `nmaGame … keygen` equals the `Pr[= true]` of
first sampling `(pk, _) ← keygen` (in plain `ProbComp`) and then running the forge-and-verify tail
through `simulateToProbComp`.

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
(`mldsaSTMSISShort_isValid_expandA_iff`); see the module docstring for the remaining
distance to the literature normal form. -/
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
binding of the recovered commitment to the hashed preimage — and record the remaining
distance to the literature SelfTargetMSIS normal form. -/

omit [DecidableEq prims.High] [DecidableEq (Commitment p prims)] [SampleableType (RqVec p.l)]
  [SampleableType (RqVec p.k)] [SampleableType (CommitHashBytes p)] in
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
  haveI := h_transform
  simp only [computeWApprox]
  exact nttOps.unhatVec_sub _ _

omit [DecidableEq (Commitment p prims)] [SampleableType (RqVec p.k)]
  [SampleableType (CommitHashBytes p)] in
/-- **What the identification verifier's accept means algebraically.** With
`c = SampleInBall(c̃)`, the verifier accepts `(w₁, c̃, (z, h))` exactly when the norm gates
`‖z‖∞ < γ₁ − β` and `weight(h) ≤ ω` hold and the published commitment `w₁` satisfies the
self-target matrix equation `UseHint(h, ExpandA(ρ)·z − c·(t₁·2^d)) = w₁` over `R_q`. In the
Fiat-Shamir game `w₁` is the very commitment hashed to produce `c̃`, so an accepted NMA
forgery carries the full literature SelfTargetMSIS relation; see the module docstring for
how much of it survives in the tailored problem `mldsaSTMSISShort`. -/
theorem identificationSchemeShort_verify_eq_true_iff (h_laws : Primitives.Laws prims nttOps)
    (pk : PublicKey p prims) (w1 : Commitment p prims) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) (h : Vector prims.Hint p.k) :
    (identificationSchemeShort p prims).verify pk w1 cTilde (z, h) = true ↔
      polyVecNorm z < p.gamma1 - p.beta ∧
      prims.hintWeight h ≤ p.omega ∧
      prims.useHintVec h (prims.expandA pk.rho * z -
        prims.sampleInBall cTilde • prims.power2RoundShiftVec pk.t1) = w1 := by
  simp only [identificationSchemeShort, identificationScheme,
    computeWApprox_eq_mul_sub_smul p prims h_laws.transform, Bool.and_eq_true,
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

omit [DecidableEq M] [SampleableType (CommitHashBytes p)] in
/-- **The algebraic bridge for the tailored SelfTargetMSIS problem.** An accepted
`mldsaSTMSISShort` solution is exactly an `stmsisAlgebraicSolution`: the verifier's norm
gates, the hint-recovered matrix equation over `R_q` with the recovered commitment `w'`
exhibited explicitly, and the self-target binding of `w'` to the commitment component of
the hashed preimage. Only the transform-isomorphism laws of `h_laws` are consumed (via
`computeWApprox_eq_mul_sub_smul`). -/
theorem mldsaSTMSISShort_isValid_iff (h_laws : Primitives.Laws prims nttOps)
    (aHat : TqMatrix p.k p.l) (pk : PublicKey p prims) (hashInput : M × Commitment p prims)
    (cTilde : CommitHashBytes p) (z : RqVec p.l) (h : Vector prims.Hint p.k) :
    (mldsaSTMSISShort p prims M).isValid aHat pk hashInput cTilde (z, h) = true ↔
      stmsisAlgebraicSolution p prims aHat pk hashInput cTilde (z, h) := by
  simp only [mldsaSTMSISShort, identificationSchemeShort, identificationScheme,
    stmsisAlgebraicSolution, computeWApprox_eq_mul_sub_smul p prims h_laws.transform,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hbind, ⟨hz, hw⟩, hweight⟩
    exact ⟨hz, hweight, _, rfl, hw, hbind⟩
  · rintro ⟨hz, hweight, w', rfl, hw, hbind⟩
    exact ⟨hbind, ⟨hz, hw⟩, hweight⟩

omit [DecidableEq M] [SampleableType (CommitHashBytes p)] in
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

/-- **The SelfTargetMSIS extractor `C` (Lemma 7, Step 3).**

`C` runs the NMA forger `main` on the public key `pk` (the STMSIS target). The forger interacts with
the random oracle `H : (M × Commitment) →ₒ CommitHashBytes`. On a forgery `(msg, some (w', (z, h)))`
`C` outputs the STMSIS preimage `(msg, w')` together with the response `(z, h)`. An aborting forgery
`(msg, none)` is mapped to a dummy preimage with a zeroed response, which the STMSIS RO-consistency
check rejects. The matrix in `params.1` is ignored by `C` (it equals `ExpandA(params.2.ρ)`).

The STMSIS experiment then looks up `c̃ = H(msg, w')` in the oracle cache and checks
`mldsaSTMSISShort.isValid Â pk (msg, w') c̃ (z, h)`, which recomputes the commitment from
`(pk, c̃, (z, h))`, requires it to equal the preimage component `w'` (the self-target binding),
and runs the identification verifier — exactly what the NMA `verify` checks after querying
`H(msg, w')`. -/
noncomputable def extractorC [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims))) :
    SelfTargetMSIS.Adversary (mldsaSTMSISShort p prims M) :=
  ⟨fun (params : TqMatrix p.k p.l × PublicKey p prims) => do
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
      return ((msg, default), default)⟩

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

/-- **Per-key STMSIS read-back comparison, short model.** For a fixed public key `pk`, the
short-model NMA forge-and-verify tail (run
through `simulateToProbComp`) accepts no more often than the SelfTargetMSIS experiment tail of
`extractorCShort` at the matching parameters `(ExpandA(ρ), pk)`. The argument never inspects
the key relation: both tails simulate `main pk` against the same random oracle from the empty
cache, an aborting forgery contributes weight `0`, and on `some (w', (z, h))` both branches
issue the same `H(msg, w')` query, whose cached answer the STMSIS experiment reads back before
`mldsaSTMSISShort.isValid` recovers the commitment, binds it to the preimage component `w'`,
and runs the identical verifier. -/
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
              hashInput hashOutput response)
        | none => pure false] := by
  classical
  -- Decompose both tails over the shared simulation of `main pk` from the empty cache.
  unfold simulateToProbComp extractorCShort extractorC
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
    -- An accepted NMA forgery is a valid STMSIS solution: the middle conjunct of `verify`
    -- says the recomputed commitment equals the forgery's `w'`, which is the commitment
    -- component of the extractor's preimage `(msg, w')` — exactly the self-target binding
    -- `isValid` demands.
    rw [probOutput_pure, probOutput_pure]
    by_cases hverify :
        (identificationSchemeShort p prims).verify pk w' cc.1 (z, h) = true
    · -- Accepted: `verify`'s middle conjunct identifies the recomputed commitment with `w'`,
      -- so the binding conjunct holds at the preimage `(msg, w')` and `verify` re-accepts at
      -- the recomputed commitment, giving `isValid = true`.
      have hvalid :
          (mldsaSTMSISShort p prims M).isValid (prims.expandA pk.rho) pk (msg, w') cc.1
            (z, h) = true := by
        simp only [mldsaSTMSISShort, identificationSchemeShort, identificationScheme]
          at hverify ⊢
        revert hverify
        grind
      rw [if_pos hverify.symm, if_pos hvalid.symm]
    · simp only [Bool.not_eq_true] at hverify
      rw [hverify]
      simp

/-- **The SelfTargetMSIS extraction bound in the idealized short-key model.** The uniform-`t`
short-model EUF-NMA advantage (key generator `keygenShort1`) is bounded by the SelfTargetMSIS
advantage of the extractor against `mldsaSTMSISShort`.

The argument is a shared-prefix read-back comparison: after the
bundled-semantics rewrite (`nmaGameShort_eq_keygen_bind`) both sides bind over the same
`keygenShort1` prefix — the short problem's `sampleParams` is definitionally `keygenShort1`
followed by publishing `(ExpandA(ρ), pk)` — so monotonicity reduces to the per-key comparison
`stmsis_tail_le_short`, which never inspects the key distribution and packages the cache
read-back and commitment recoverability. -/
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

  `Adv^{EUF-NMA}(A) ≤ Adv^{MLWE}(B) + Adv^{SelfTargetMSIS}(C)`.

The reductions are the concrete ones built in this file: the key-swap distinguisher
`distinguisherBShort`, whose `mldsaMLWEShort` advantage **equals** the real-vs-uniform key gap —
the short key-swap hop `nma_keyswap_hop_short` is an exact monad identity, so no statistical
slack term appears in the bound — and the SelfTargetMSIS extractor `extractorCShort`, which
turns a uniform-`t` forgery into a short self-target solution
(`nmaAdvantage_keygenShort1_le_stmsis`).

The hypothesis `hMlweBridge` supplies, for every forging strategy, an abstract MLWE adversary at
a bridge slack `εbridge`. Its canonical discharge lands on the uniform-matrix problem: take
`mlwe := mldsaMatrixMLWE p`, `εbridge := εA`, and for each `main` the witness
`matrixLift p prims (distinguisherBShort p prims hr maxAttempts main)` with the proven reduction
`advantage_mldsaMLWEShort_le_matrix` under the `expandAIdealization εA` assumption.

Concretely, it supplies for every forging strategy an abstract MLWE adversary at
least as good (up to `εbridge`) as `distinguisherBShort` against the seed-based short problem
`mldsaMLWEShort` — the
distribution the ML-DSA Module-LWE assumption is stated over (secrets uniform on the `η`-bounded
box). Under `expandAIdealization` the bridge can be instantiated against the standard
uniform-matrix problem `mldsaMatrixMLWE` via `advantage_mldsaMLWEShort_le_matrix`. The
SelfTargetMSIS side has matching types, so `hStmsis` is a plain equality
`stmsis = mldsaSTMSISShort p prims M`, and `hGen : hr.gen = keygenShort p prims` pins the
Fiat-Shamir key generation to the idealized short-key generator. The relation of `hr` is the
material-based `validKeyPairShort`, which `keygenShort` genuinely generates: the pair
`(hr, hGen)` is inhabited by `hrShort` (`keygenShort_generable`), so the statement has
non-vacuous instances.

This is the EUF-NMA half (Lemma 7) of the ML-DSA security proof in the idealized short-key model;
the CMA-to-NMA statistical step (`euf_cma_security_of_nma_short`) composes on top of it. -/
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

The short-model bound `nma_security_short` transferred to the deterministic FIPS key
generator `keygen0` through the XOF-replacement assumption `expandSReplacement`: for every
EUF-NMA adversary against the ML-DSA scheme instantiated with the seed-derived key relation
(`hGen : hr.gen = keygen0 p prims`, inhabited by `hrFips` / `keygen0_generable`), there are
an MLWE adversary and a SelfTargetMSIS adversary with

  `Adv^{EUF-NMA}(A) ≤ (Adv^{MLWE}(B) + εbridge) + Adv^{SelfTargetMSIS}(C) + εPRG`.

The proof has exactly one new ingredient beyond the short model: the FIPS and short NMA
games share their forge-and-verify tail (`identificationScheme` and
`identificationSchemeShort` carry the same `verify` function), so the gap between the
`keygen0` game and the `keygenShort` game is one application of `hPRG` at the distinguisher
`D ρ K s₁ s₂ :=` "run the tail at the key built by `keyFromMaterial` from the material
`(ρ, K, s₁, s₂)`": its real branch is exactly the FIPS game and its ideal branch is exactly
the short game. The short-model reduction hypotheses (`hrS`/`hGenS`, `hStmsis`,
`hMlweBridge`) then bound the short game as in `nma_security_short`, applied to the same
forging strategy repackaged at the short scheme tag. -/
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

open scoped Classical in
/-- **EUF-CMA security of ML-DSA in the idealized short-key model, wired end to end.**

The CMA-to-NMA-to-hardness composition over the idealized short-secret key generation
`keygenShort`: for any EUF-CMA adversary `adv` against the Fiat-Shamir-with-aborts ML-DSA
signature, the advantage is bounded by the MLWE advantage, the SelfTargetMSIS advantage, and the
statistical CMA-to-NMA loss `FiatShamirWithAbort.cmaToNmaLoss`. The proof composes three pieces:

1. `FiatShamirWithAbort.euf_cma_to_nma`: `adv.advantage ≤ Pr[managedRoNmaExp simulatedNmaAdv]
   + cmaToNmaLoss`, under the good-key/commitment-guessing/abort/query hypotheses;
2. `FiatShamirWithAbort.managedRoNmaExp_simulatedNmaAdv_eq_eufNmaExp` (Option B): the managed-RO
   NMA success probability equals the plain EUF-NMA advantage of `simulatedEufNmaAdv`, the
   cache-forgetting reduction;
3. `nma_security_short` (Lemma 7, short model) applied to `simulatedEufNmaAdv`:
   `≤ MLWE + SelfTargetMSIS`, with no statistical key-swap slack — the short-model hop is exact.

The loss parameters carry the nonnegativity and good-key hypotheses that the abstract reduction
needs; the bridge hypotheses (`hGen`, `hStmsis`, `hMlweBridge`) pin the abstract hardness problems
to the concrete short-model ML-DSA ones (`keygenShort`, `mldsaSTMSISShort`, `mldsaMLWEShort`).
The relation of `hr` is the material-based `validKeyPairShort`, so `hGen` is inhabited by
`hrShort` (`keygenShort_generable`). The HVZK obligation `hhvzk` stays abstract: in the short
model the withheld key part `t₀` is not determined by the public key across material-valid
pairs, so no single simulator is exact-on-accept for every valid pair; the hypothesis is
satisfiable (any simulator at `ζ_zk = 1`, since `tvDist ≤ 1`), and a quantitative discharge
needs a bound accounting for the hint mismatch across colliding keys. -/
theorem euf_cma_security_of_nma_short [SampleableType (PublicKey p prims)]
    (mlwe : LearningWithErrors.Problem (TqMatrix p.k p.l) (RqVec p.l) (RqVec p.k))
    (stmsis : SelfTargetMSIS.Problem
      (TqMatrix p.k p.l) (Response p prims)
      (PublicKey p prims) (M × Commitment p prims) (CommitHashBytes p))
    (maxAttempts : ℕ)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p)
      (validKeyPairShort p prims))
    (hGen : hr.gen = keygenShort p prims)
    (hStmsis : stmsis = mldsaSTMSISShort p prims M)
    (sim : PublicKey p prims →
      ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk)
    (hhvzk : (identificationSchemeShort p prims).HVZK sim ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : PublicKey p prims → SecretKey p → Prop)
    (hGood : Pr[ fun xw : PublicKey p prims × SecretKey p => ¬ Good xw.1 xw.2 | hr.gen] ≤
      ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commitment p prims,
      Pr[= cm | Prod.fst <$> (identificationSchemeShort p prims).commit pk sk] ≤
        ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr[= none | (identificationSchemeShort p prims).honestExecution pk sk] ≤
        ENNReal.ofReal p_abort)
    (hAbortSim : ∀ pk sk, Good pk sk →
      Pr[= none | sim pk] ≤ ENNReal.ofReal p_abort)
    (adv : SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts))
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commitment p prims × Response p prims)) (oa := adv.main pk) qS qH)
    (εbridge : ℝ)
    (hMlweBridge : ∀ (main : PublicKey p prims →
        OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
          (M × Option (Commitment p prims × Response p prims))),
      ∃ B : LearningWithErrors.Adversary mlwe,
        LearningWithErrors.advantage (mldsaMLWEShort p prims)
          (distinguisherBShort p prims hr maxAttempts main) ≤
          LearningWithErrors.advantage mlwe B + εbridge) :
    ∃ (mlweReduction : LearningWithErrors.Adversary mlwe)
      (stmsisReduction : SelfTargetMSIS.Adversary stmsis),
      adv.advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal (LearningWithErrors.advantage mlwe mlweReduction + εbridge) +
        SelfTargetMSIS.advantage stmsisReduction +
        ENNReal.ofReal
          (FiatShamirWithAbort.cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  classical
  -- Step 1: CMA advantage ≤ managed-RO NMA success of `simulatedNmaAdv` + loss.
  have hcma := FiatShamirWithAbort.euf_cma_to_nma (identificationSchemeShort p prims) hr M
    maxAttempts sim adv ζ_zk hζ hhvzk qS qH ε p_abort δ hε hδ hp₀ hp Good hGood hGuess
    hAbort hAbortSim hQ
  -- Step 2 (Option B bridge): managed-RO NMA success = plain EUF-NMA advantage of the
  -- cache-forgetting reduction `simulatedEufNmaAdv`.
  have hbridge := FiatShamirWithAbort.managedRoNmaExp_simulatedNmaAdv_eq_eufNmaExp
    (identificationSchemeShort p prims) hr M maxAttempts sim adv
  -- Step 3 (Lemma 7, short model): the plain EUF-NMA advantage is bounded by MLWE + STMSIS.
  obtain ⟨mlweRed, stmsisRed, hnma⟩ := nma_security_short p prims mlwe stmsis maxAttempts
    hr hGen hStmsis εbridge hMlweBridge
    (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeShort p prims) hr M
      maxAttempts sim adv)
  refine ⟨mlweRed, stmsisRed, ?_⟩
  -- Assemble: advantage ≤ (managed = eufNma advantage ≤ MLWE + STMSIS) + loss.
  refine le_trans hcma ?_
  have hmanaged : Pr[= true | SignatureAlg.managedRoNmaExp
        (FiatShamirWithAbort.runtime M)
        (FiatShamirWithAbort.simulatedNmaAdv (identificationSchemeShort p prims) hr M
          maxAttempts sim adv)] =
      (FiatShamirWithAbort.simulatedEufNmaAdv (identificationSchemeShort p prims) hr M
        maxAttempts sim adv).advantage (FiatShamirWithAbort.runtime M) := by
    rw [SignatureAlg.eufNmaAdv.advantage, hbridge]
  rw [hmanaged]
  exact add_le_add hnma le_rfl

/-! ## Asymptotic (negligible) EUF-CMA headline

The non-degenerate asymptotic statement. The scheme is indexed by a security parameter `n`
through a *family* `(p n, prims n)` of ML-DSA parameter/primitive instances, so that the
commitment guessing probability `ε n`, the key-regularity failure `δ n`, the HVZK slack
`ζ_zk n`, and the MLWE-bridge slack `εbridge n` all shrink (negligibly) as `n → ∞` while the
signing / hashing query budgets `qS n`, `qH n` grow only polynomially in `n`. Under negligible
MLWE and SelfTargetMSIS advantage families this makes the EUF-CMA advantage family negligible.

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
/-- **Asymptotic (negligible) EUF-CMA security of ML-DSA in the idealized short-key model.**

The security-parameter-indexed, non-degenerate headline. The ML-DSA scheme is given as a
*family* `(p n, prims n)` over the security parameter `n`, with all carrier instances
supplied per `n`. The hypotheses are the `n`-indexed lifts of those of
`euf_cma_security_of_nma_short`, plus:

* polynomial query bounds `qS n ≤ pS.eval n`, `qH n ≤ pH.eval n`;
* negligible commitment-guessing slack `ε`, key-regularity slack `δ`, HVZK slack `ζ_zk`,
  and MLWE-bridge slack `εbridge` families (the commitment / response spaces grow with `n`);
* negligible MLWE and SelfTargetMSIS advantage families `mlweAdv`, `stmsisAdv` dominating
  every reduction adversary (the hardness assumptions, carried as `n`-indexed families per
  the standard ROM model).

The conclusion is that the EUF-CMA advantage family of `adv` is negligible. The proof
instantiates the per-`n` bound `euf_cma_security_of_nma_short`, dominates the two existential
reductions by their negligible families, and bounds the statistical loss family with
`cmaToNmaLoss_negligible`: with polynomially-bounded queries and negligible slacks each loss
term is `poly(n) · negligible(n)`.

No cost model is attached: the statement quantifies over unrestricted adversaries and
`n`-indexed advantage families, not over poly-time adversaries (see the scope note in the
module docstring). The numerical regime is jointly satisfiable with genuinely growing query
budgets (`asymptotic_loss_regime_satisfiable`). -/
theorem euf_cma_security_asymptotic_short
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
    (mlwe : ∀ n, LearningWithErrors.Problem (TqMatrix (p' n).k (p' n).l)
      (RqVec (p' n).l) (RqVec (p' n).k))
    (stmsis : ∀ n, SelfTargetMSIS.Problem
      (TqMatrix (p' n).k (p' n).l) (Response (p' n) (prims' n))
      (PublicKey (p' n) (prims' n)) (M' × Commitment (p' n) (prims' n))
      (CommitHashBytes (p' n)))
    (maxAttempts : ℕ → ℕ)
    (hr : ∀ n, GenerableRelation (PublicKey (p' n) (prims' n)) (SecretKey (p' n))
      (validKeyPairShort (p' n) (prims' n)))
    (hGen : ∀ n, (hr n).gen = keygenShort (p' n) (prims' n))
    (hStmsis : ∀ n, stmsis n = mldsaSTMSISShort (p' n) (prims' n) M')
    (sim : ∀ n, PublicKey (p' n) (prims' n) → ProbComp
      (Option (Commitment (p' n) (prims' n) × CommitHashBytes (p' n) ×
        Response (p' n) (prims' n))))
    (ζ_zk : ℕ → ℝ) (hζ : ∀ n, 0 ≤ ζ_zk n)
    (hhvzk : ∀ n, (identificationSchemeShort (p' n) (prims' n)).HVZK (sim n) (ζ_zk n))
    (qS qH : ℕ → ℕ) (ε δ : ℕ → ℝ) (p_abort : ℝ)
    (hp : p_abort < 1) (hp₀ : 0 ≤ p_abort)
    (hε : ∀ n, 0 ≤ ε n) (hδ : ∀ n, 0 ≤ δ n)
    (Good : ∀ n, PublicKey (p' n) (prims' n) → SecretKey (p' n) → Prop)
    (hGood : ∀ n, Pr[ fun xw : PublicKey (p' n) (prims' n) × SecretKey (p' n) =>
        ¬ Good n xw.1 xw.2 | (hr n).gen] ≤ ENNReal.ofReal (δ n))
    (hGuess : ∀ n, ∀ pk sk, Good n pk sk → ∀ cm : Commitment (p' n) (prims' n),
      Pr[= cm | Prod.fst <$> (identificationSchemeShort (p' n) (prims' n)).commit pk sk] ≤
        ENNReal.ofReal (ε n))
    (hAbort : ∀ n, ∀ pk sk, Good n pk sk →
      Pr[= none | (identificationSchemeShort (p' n) (prims' n)).honestExecution pk sk] ≤
        ENNReal.ofReal p_abort)
    (hAbortSim : ∀ n, ∀ pk sk, Good n pk sk →
      Pr[= none | sim n pk] ≤ ENNReal.ofReal p_abort)
    (adv : ∀ n, SignatureAlg.unforgeableAdv
      (FiatShamirWithAbort (identificationSchemeShort (p' n) (prims' n)) (hr n) M'
        (maxAttempts n)))
    (hQ : ∀ n, ∀ pk, FiatShamir.signHashQueryBound M'
      (S' := Option (Commitment (p' n) (prims' n) × Response (p' n) (prims' n)))
      (oa := (adv n).main pk) (qS n) (qH n))
    (εbridge : ℕ → ℝ)
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
      ENNReal.ofReal (LearningWithErrors.advantage (mlwe n) B) ≤ mlweAdv n)
    (hStmsisBound : ∀ n (C : SelfTargetMSIS.Adversary (stmsis n)),
      SelfTargetMSIS.advantage C ≤ stmsisAdv n)
    (hbridgeNegl : negligible (fun n => ENNReal.ofReal (εbridge n)))
    (hεneg : negligible (fun n => ENNReal.ofReal (ε n)))
    (hδneg : negligible (fun n => ENNReal.ofReal (δ n)))
    (hζneg : negligible (fun n => ENNReal.ofReal (ζ_zk n))) :
    negligible (fun n => (adv n).advantage
      (FiatShamirWithAbort.runtime
        (Commit := Commitment (p' n) (prims' n)) (Chal := CommitHashBytes (p' n)) M')) := by
  have hbound : ∀ n, (adv n).advantage
      (FiatShamirWithAbort.runtime
        (Commit := Commitment (p' n) (prims' n)) (Chal := CommitHashBytes (p' n)) M') ≤
      mlweAdv n + ENNReal.ofReal (εbridge n) + stmsisAdv n +
      ENNReal.ofReal (FiatShamirWithAbort.cmaToNmaLoss (qS n) (qH n) (ε n) p_abort
        (ζ_zk n) (δ n) hp) := by
    intro n
    obtain ⟨mlweRed, stmsisRed, hb⟩ :=
      @euf_cma_security_of_nma_short (p' n) (prims' n) nttOps' (instHigh n) M' _
        (instCommEq n) (instCommInh n) (instRespInh n) (instRql n) (instRqk n)
        (instChal n) (instPk n)
        (mlwe n) (stmsis n) (maxAttempts n) (hr n) (hGen n) (hStmsis n)
        (sim n) (ζ_zk n) (hζ n) (hhvzk n)
        (qS n) (qH n) (ε n) p_abort (δ n) (hε n) (hδ n) hp₀ hp (Good n) (hGood n) (hGuess n)
        (hAbort n) (hAbortSim n) (adv n) (hQ n) (εbridge n) (hMlweBridge n)
    refine le_trans hb ?_
    have h1 : ENNReal.ofReal (LearningWithErrors.advantage (mlwe n) mlweRed + εbridge n) ≤
        mlweAdv n + ENNReal.ofReal (εbridge n) :=
      le_trans ENNReal.ofReal_add_le (add_le_add (hMlweBound n mlweRed) le_rfl)
    exact add_le_add (add_le_add h1 (hStmsisBound n stmsisRed)) le_rfl
  refine negligible_of_le hbound ?_
  refine negligible_add (negligible_add (negligible_add hmlweNegl hbridgeNegl) hstmsisNegl) ?_
  exact cmaToNmaLoss_negligible qS qH ε ζ_zk δ p_abort hp pS pH hqS hqH hεneg hζneg hδneg

omit nttOps in
/-- **Consistency of the asymptotic numerical-loss regime.**

The quantitative hypotheses of `euf_cma_security_asymptotic_short` — *polynomially-bounded*
query budgets together with *negligible* statistical slacks (commitment guessing `ε`, HVZK
`ζ_zk`, key regularity `δ`, MLWE bridge `εbridge`) and negligible hardness advantage families
— are jointly satisfiable with query budgets that genuinely **grow** with the security
parameter. Concretely, taking `qS n = qH n = n` (bounded by `Polynomial.X`, i.e. *not*
vanishing), all slacks and advantage families equal to `(1 / 2) ^ n`, and `p_abort = 1 / 2`,
the resulting `cmaToNmaLoss` family, together with the two hardness families and the bridge
slack, is negligible — so the dominating sum in the headline's internal bound is negligible.

This rules out the degenerate reading of the headline (where polynomial queries against a
*fixed* positive `ε` would force the budgets to vanish): here the budgets grow polynomially
while the loss still decays.

This statement chooses **numerical sequences only**. It does not instantiate the hardness
problems, `hMlweBridge`, the HVZK simulator family, the scheme family, or the other
hypotheses of `euf_cma_security_asymptotic_short`; it describes the loss regime, not the
satisfiability of the security theorem. -/
theorem asymptotic_loss_regime_satisfiable :
    ∃ (qS qH : ℕ → ℕ) (ε ζ_zk δ εbridge : ℕ → ℝ) (p_abort : ℝ) (hp : p_abort < 1)
      (pS pH : Polynomial ℕ) (mlweAdv stmsisAdv : ℕ → ℝ≥0∞),
      (∀ n, qS n ≤ pS.eval n) ∧ (∀ n, qH n ≤ pH.eval n) ∧
      -- the queries genuinely grow (are not the degenerate vanishing-query regime)
      (∀ n, qS n = n) ∧ (∀ n, qH n = n) ∧
      negligible mlweAdv ∧ negligible stmsisAdv ∧
      negligible (fun n => ENNReal.ofReal (ε n)) ∧
      negligible (fun n => ENNReal.ofReal (ζ_zk n)) ∧
      negligible (fun n => ENNReal.ofReal (δ n)) ∧
      negligible (fun n => ENNReal.ofReal (εbridge n)) ∧
      negligible (fun n => mlweAdv n + ENNReal.ofReal (εbridge n) + stmsisAdv n +
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
    hnegE, hnegE, hneg, hneg, hneg, hneg, ?_⟩
  refine negligible_add (negligible_add (negligible_add hnegE hneg) hnegE) ?_
  exact cmaToNmaLoss_negligible (fun n => n) (fun n => n) (fun n => (1 / 2) ^ n)
    (fun n => (1 / 2) ^ n) (fun n => (1 / 2) ^ n) (1 / 2) (by norm_num) Polynomial.X Polynomial.X
    hgrow hgrow hneg hneg hneg

end Headline

/-! ## Status

The short-model headline `nma_security_short` is proven and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), assembled from:

1. **Exact MLWE key-swap (`nma_keyswap_hop_short`).** `(Hadv)` is the generic
   `advantage_eq_game_boolDistAdvantage`; both branch identifications are pure
   runtime-plumbing rewrites (`nmaGameShort_eq_keygen_bind` plus stripping the unused leading
   draws), because `keygenShort`/`keygenShort1` sample `ρ`, `K`, `s₁`, `s₂` independently
   exactly as `mldsaMLWEShort`'s `distr`/`uniformDistr` do. No statistical slack appears.

2. **STMSIS extraction (`nmaAdvantage_keygenShort1_le_stmsis`).** Both `Pr[= true]`s reduce,
   through the shared `withStateOracle` semantics, to: sample the uniform-`t` key, run the
   forger against the RO, and on `some (w', (z,h))` read `c̃ = H(msg, w')` from the cache and
   accept iff `ids.verify pk w' c̃ (z,h)`. After `nmaGameShort_eq_keygen_bind` both sides bind
   over the same `keygenShort1` prefix, so `probOutput_bind_mono` reduces to the per-key lemma
   `stmsis_tail_le_short`, which decomposes both tails over the shared `main pk` simulation,
   gives weight `0` to the aborting branch, and on a non-aborting forgery couples the single
   `H(msg, w')` query — the cached answer is read back
   (`QueryImpl.withCaching_run_some`/`_none`, `QueryCache.cacheQuery_self`) and
   `verify = true → isValid = true` (the middle conjunct of `verify` identifies the
   recomputed commitment with the hashed preimage's component `w'`, discharging the
   self-target binding) closes the per-answer inequality.

3. **Bridges.** `nma_security_short` quantifies over an *abstract* `mlwe`, an *abstract*
   `stmsis`, and an *abstract* `hr`; the bridge hypotheses are part of the statement:
   `hGen : hr.gen = keygenShort p prims` (inhabited by `keygenShort_generable`),
   `hStmsis : stmsis = mldsaSTMSISShort p prims M`, and `hMlweBridge` at a slack `εbridge`,
   canonically discharged against the uniform-matrix `mldsaMatrixMLWE` via
   `advantage_mldsaMLWEShort_le_matrix` under `expandAIdealization`.

4. **FIPS transfer (`nma_security_fips`).** The `keygen0` game differs from the `keygenShort`
   game by one application of the `expandSReplacement` distinguisher at the shared
   forge-and-verify tail, adding `εPRG` to the bound (`hGen` at the seed relation is
   inhabited by `keygen0_generable`). Supplying a concrete quantitative `εPRG` for a concrete
   `prims` is a modeling decision pending the cost-model infrastructure (#460).
-/

section MatrixHeadline

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]
  {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
  [SampleableType (RqVec p.l)] [SampleableType (RqVec p.k)]
  [SampleableType (TqMatrix p.k p.l)]
  [SampleableType (CommitHashBytes p)]

/-- **The literature-facing NMA headline.** `nma_security_short` with the abstract-problem
bridge discharged: the MLWE leg lands on the standard uniform-matrix short-secret problem
`mldsaMatrixMLWE`, at the cost of one application of the `expandAIdealization` assumption
(`advantage_mldsaMLWEShort_le_matrix`, supplying the bridge slack `εA`), and the
SelfTargetMSIS leg on `mldsaSTMSISShort`. No caller-supplied inequality remains: every
hypothesis is a satisfiable pinned equality (`keygenShort_generable`), a proven reduction,
or the named XOF idealization. -/
theorem nma_security_short_matrix (maxAttempts : ℕ) (εA : ℝ)
    (hA : NMA.expandAIdealization p prims εA)
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (hGen : hr.gen = NMA.keygenShort p prims) :
    ∀ (adv : SignatureAlg.eufNmaAdv
      (FiatShamirWithAbort (identificationSchemeShort p prims) hr M maxAttempts)),
    ∃ (mlweReduction : LearningWithErrors.Adversary (NMA.mldsaMatrixMLWE p))
      (stmsisReduction : SelfTargetMSIS.Adversary (NMA.mldsaSTMSISShort p prims M)),
      adv.advantage
          (FiatShamirWithAbort.runtime
            (Commit := Commitment p prims) (Chal := CommitHashBytes p) M) ≤
        ENNReal.ofReal
          (LearningWithErrors.advantage (NMA.mldsaMatrixMLWE p) mlweReduction + εA) +
        SelfTargetMSIS.advantage stmsisReduction :=
  nma_security_short p prims (NMA.mldsaMatrixMLWE p) (NMA.mldsaSTMSISShort p prims M)
    maxAttempts hr hGen rfl εA
    (fun main => ⟨NMA.matrixLift p prims (NMA.distinguisherBShort p prims hr maxAttempts main),
      NMA.advantage_mldsaMLWEShort_le_matrix p prims hA _⟩)

end MatrixHeadline

end MLDSA
