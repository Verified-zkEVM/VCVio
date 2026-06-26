/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
import VCVio.ProgramLogic.Relational.ProgrammingOracle

/-!
# GPV Hash-and-Sign Framework

This file defines a generic hash-and-sign signature scheme following the GPV (Gentry–Peikert–
Vaikuntanathan) framework [GPV08]. The construction is parameterized by a *preimage sampleable
function* (PSF), a many-to-one function equipped with a probabilistic trapdoor that samples
short preimages.

The GPV framework is the hash-and-sign analogue of the Fiat-Shamir transform:

| Interactive protocol | Fiat-Shamir → SignatureAlg |
|---|---|
| Trapdoor PSF | GPVHashAndSign → SignatureAlg |

## Main Definitions

- `PreimageSampleableFunction` — a function `eval` with a probabilistic trapdoor sampler and a
  shortness predicate on preimages.
- `GPVHashAndSign` — builds a `SignatureAlg` in the random-oracle model from a PSF, a generable
  key relation, and a salt type.

## Security

The PFDH (Probabilistic Full-Domain Hash) variant of the GPV scheme uses a random salt per
signing query. The precise EUF-CMA bound from [FGdG+25] Theorem 1 is:

  `Adv^{UF-CMA}(A) ≤ (r_u^{C_s} · (r_p^{C_s} · Adv^{ISIS}(B))^{...})^{...}`
  `                  + tail_bound + Q_s · (C_s + Q_H) / 2^k`

where the salt-collision term `Q_s · (C_s + Q_H) / 2^k` bounds the probability that
a fresh salt collides with any prior RO query. The simpler birthday bound
`qSign² / (2 · |Salt|)` from GPV08 Prop 6.2 is slightly looser but still valid and is
the one we formalize here.

The proof decomposes into:
- `GPVHashAndSign.reduction`: the collision-finding adversary (sign-then-hash simulation)
- `GPVHashAndSign.programmedPreimageReduction`: the exact-match branch reduction
- `GPVHashAndSign.collisionBound`: the salt-collision birthday bound
- `GPVHashAndSign.forgery_yields_collision`: the core distinct-preimage game-hop
- `GPVHashAndSign.forgery_yields_collision_or_exact_match`: the explicit split bound

## References

- [FGdG+25]: Fouque, Gajland, de Groote, Janneck, Kiltz. "A Closer Look at Falcon."
  ePrint 2024/1769. First concrete proof for Falcon+ (Theorem 1).
- [Jia+26]: Jia, Zhang, Yu, Tang. "Revisiting the Concrete Security of Falcon-type
  Signatures." ePrint 2026/096. Tightens Rényi loss to < 0.2 bits.
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008, Propositions 6.1–6.2.
- BDF+11: Boneh et al. "Random Oracles in a Quantum World." ASIACRYPT 2011.
-/

universe v


open OracleComp OracleSpec ENNReal OracleComp.ProgramLogic.Relational

/-! ## Preimage Sampleable Functions -/

/-- A preimage sampleable function (PSF) consists of:
- A public evaluation map `eval : PK → Domain → Range`.
- A probabilistic trapdoor sampler `trapdoorSample` that, given the secret key and a target in
  the range, produces a preimage in the domain.
- A shortness predicate `isShort` that the verifier checks on purported preimages.

This abstracts the core primitive in the GPV hash-and-sign framework. Unlike
`TrapdoorPermutation` (in `OneWay.lean`), a PSF is many-to-one, the inversion is probabilistic,
and acceptance depends on a quality predicate rather than exact inversion. -/
structure PreimageSampleableFunction (PK SK Domain Range : Type) where
  eval : PK → Domain → Range
  trapdoorSample : PK → SK → Range → ProbComp Domain
  isShort : Domain → Bool

namespace PreimageSampleableFunction

variable {PK SK Domain Range : Type}

/-- A PSF is correct if the trapdoor sampler always produces a valid preimage that is
accepted by the shortness predicate. -/
def Correct (psf : PreimageSampleableFunction PK SK Domain Range) : Prop :=
  ∀ pk sk t, ∀ x ∈ support (psf.trapdoorSample pk sk t),
    psf.eval pk x = t ∧
      psf.isShort x = true

/-- A PSF is correct *at a fixed key pair* `(pk, sk)` if the trapdoor sampler at that key always
produces a valid preimage that is accepted by the shortness predicate. This is the per-key slice of
`Correct`: `Correct psf` is definitionally `∀ pk sk, psf.CorrectAt pk sk`. -/
def CorrectAt (psf : PreimageSampleableFunction PK SK Domain Range) (pk : PK) (sk : SK) : Prop :=
  ∀ (t : Range) (x : Domain), x ∈ support (psf.trapdoorSample pk sk t) →
    psf.eval pk x = t ∧ psf.isShort x = true

/-- The GPV *regularity* (preimage-sampleability) property, expressed externally as an
equality of joint distributions.

A PSF is regular when there is a domain sampler `domainSample : PK → ProbComp Domain` such
that, for every key pair `(pk, sk)`, the joint distribution of `(eval pk s, s)` for a
forward-sampled preimage `s ← domainSample pk` matches the joint distribution of `(c, s)`
where the target `c` is drawn uniformly from `Range` and `s ← trapdoorSample pk sk c` is the
trapdoor preimage of `c`.

This is the classical GPV08 preimage-sampleability requirement: sampling a short preimage and
hashing it forward is statistically identical to sampling a uniform target and inverting it
with the trapdoor. It is the hypothesis that justifies the sign-then-hash hop in the EUF-CMA
proof. It is entered as an external hypothesis rather than as a field of
`PreimageSampleableFunction`, so the generic GPV theorem stays loss-free and each concrete
instance (e.g. Falcon) accounts for any sampler imperfection separately.

The property is satisfiable in principle: when `eval pk` is a bijection,
`trapdoorSample pk sk c := pure ((eval pk)⁻¹ c)` and `domainSample pk := $ᵗ Domain` realize
the equality. It is also non-trivial: the equation genuinely constrains `domainSample` against
the trapdoor sampler, so it is not vacuously true. -/
def Regularity [SampleableType Range]
    (psf : PreimageSampleableFunction PK SK Domain Range) : Prop :=
  ∃ domainSample : PK → ProbComp Domain,
    ∀ (pk : PK) (sk : SK),
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]

end PreimageSampleableFunction

/-! ## GPV Hash-and-Sign Construction -/

/-- The GPV hash-and-sign signature scheme in the random-oracle model.

Given a preimage sampleable function `psf`, a generable key relation `hr`, and a salt type
`Salt`, the construction builds a `SignatureAlg` where:

- **`keygen`**: sample a key pair from `hr.gen`.
- **`sign pk sk m`**: sample a random salt `r`, query the random oracle at `(r, m)` to obtain
  a target `c`, use `trapdoorSample` to find a short preimage `s` of `c`, and return `(r, s)`.
- **`verify pk m (r, s)`**: recompute `c` from the random oracle at `(r, m)`, then check that
  `eval pk s = c` and `isShort s`.

The signature type is `Salt × Domain` (salt paired with the short preimage).
The oracle spec is `unifSpec + (Salt × M →ₒ Range)` (uniform sampling + random oracle). -/
def GPVHashAndSign
    {m : Type → Type v} [Monad m]
    {PK SK Domain Range : Type}
    (psf : PreimageSampleableFunction PK SK Domain Range)
    {p : PK → SK → Bool}
    (hr : GenerableRelation PK SK p)
    (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]
    [DecidableEq Range] [SampleableType Range]
    [MonadLiftT ProbComp m] [MonadLiftT (OracleQuery (Salt × M →ₒ Range)) m] :
    SignatureAlg m
      (M := M) (PK := PK) (SK := SK) (S := Salt × Domain) where
  keygen := liftM hr.gen
  sign := fun pk sk msg => do
    let r ← ($ᵗ Salt : ProbComp Salt)
    let c ← (Salt × M →ₒ Range).query (r, msg)
    let s ← psf.trapdoorSample pk sk c
    pure (r, s)
  verify := fun pk msg (r, s) => do
    let c ← (Salt × M →ₒ Range).query (r, msg)
    pure (decide (psf.eval pk s = c) && psf.isShort s)

namespace GPVHashAndSign

variable {PK SK Domain Range : Type}
  {p : PK → SK → Bool}
  [DecidableEq Range] [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p)
  (M Salt : Type) [DecidableEq M] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt]

/-- Runtime bundle for the GPV hash-and-sign random-oracle world. -/
noncomputable def runtime :
    ProbCompRuntime (OracleComp (unifSpec + (Salt × M →ₒ Range))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (Salt × M →ₒ Range) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
    ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Structural bound that counts only random-oracle queries in a GPV EUF-CMA adversary.

Defined as the generic predicate-targeted query bound `IsQueryBoundP` with the predicate
selecting the nested `.inl (.inr _)` (random-oracle) component of the index sum. -/
def hashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ S')) α) (Q : ℕ) : Prop :=
  OracleComp.IsQueryBoundP oa (· matches .inl (.inr _)) Q

/-- Structural query bound for GPV EUF-CMA adversaries that tracks both signing-oracle
queries (`qSign`) and random-oracle queries (`qHash`). Uniform-sampling queries are
unrestricted.

Defined as the conjunction of two predicate-targeted query bounds `IsQueryBoundP`, one per
counted oracle. Because the two index predicates are disjoint, the conjunction is
equivalent to the prior single-vector `IsQueryBound` formulation. -/
def signHashQueryBound {S' α : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ S')) α)
    (qSign qHash : ℕ) : Prop :=
  oa.IsQueryBoundP (· matches .inr _) qSign ∧
  oa.IsQueryBoundP (· matches .inl (.inr _)) qHash

/-- A collision-finding adversary receives a public key and must produce two distinct
short preimages with the same image under `psf.eval`. -/
abbrev CollisionAdversary := PK → ProbComp (Domain × Domain)

/-- Keyed collision-finding experiment for a preimage sampleable function. -/
def collisionFindingExp [DecidableEq Domain]
    (adversary : CollisionAdversary (PK := PK) (Domain := Domain)) :
    ProbComp Bool := do
  let pk ← do
    let keyPair ← hr.gen
    pure keyPair.1
  let (x₁, x₂) ← adversary pk
  return decide (x₁ ≠ x₂) &&
    decide (psf.eval pk x₁ = psf.eval pk x₂) &&
    psf.isShort x₁ &&
    psf.isShort x₂

/-- Success probability in the keyed collision-finding experiment. -/
noncomputable def collisionFindingAdvantage [DecidableEq Domain]
    (adversary : CollisionAdversary (PK := PK) (Domain := Domain)) :
    ℝ≥0∞ :=
  Pr[= true | collisionFindingExp (psf := psf) (hr := hr) adversary]

/-- A programmed-preimage adversary receives a public key and a programmed target `y`,
and tries to reproduce the challenger's hidden short preimage sampled for `y`. -/
abbrev ProgrammedPreimageAdversary := PK → Range → ProbComp Domain

/-- Exact-match experiment for the hidden programmed-preimage branch of the GPV proof.

The challenger samples an honest key pair, then chooses a uniformly random target `y` and a
hidden short preimage `x ← trapdoorSample pk sk y`. The adversary sees only `(pk, y)` and
succeeds iff it reproduces exactly the hidden programmed preimage `x`. -/
def programmedPreimageExp [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range)) :
    ProbComp Bool := do
  let (pk, sk) ← hr.gen
  let y ← $ᵗ Range
  let x ← psf.trapdoorSample pk sk y
  let x' ← adversary pk y
  return decide (x' = x)

/-- Success probability in the exact-match programmed-preimage experiment. -/
noncomputable def programmedPreimageAdvantage [DecidableEq Domain]
    (adversary : ProgrammedPreimageAdversary
      (PK := PK) (Domain := Domain) (Range := Range)) :
    ℝ≥0∞ :=
  Pr[= true | programmedPreimageExp (psf := psf) (hr := hr) adversary]

/-! ## Proof Decomposition

The EUF-CMA security proof proceeds by a game-hopping argument:

**Game 0**: The real EUF-CMA experiment with a lazy random oracle and the honest
signing oracle (trapdoor sampler).

**Game 1**: Replace signing with "sign-then-hash": for each signing query on message `m`,
sample a short preimage `s ← D_short`, set `c := psf.eval pk s`, program the RO at
`(r, m) := c`, and return `(r, s)`. This is indistinguishable from Game 0 when the PSF
sampler is correct (the output distribution conditioned on the target is the same).

**Bad event**: A salt collision occurs (two distinct signing queries or the forgery reuse
the same `(salt, message)` pair as a prior RO entry). Under the birthday bound, this
happens with probability at most `q_S² / (2 · |Salt|)`.

**Game 2 (reduction)**: The simulator programs the random oracle with hidden short preimages.
If the adversary forges on a fresh `(salt, message)` pair and the forged short preimage differs
from the simulator's hidden programmed preimage at that point, the pair forms a collision under
`psf.eval`.

The exact-match branch, where the forgery reproduces the simulator's programmed preimage, is a
separate one-way/min-entropy obligation and is intentionally not encoded in the collision game
below.
-/

/-- The collision-branch GPV reduction adversary. Given a public key `pk`,
the reduction internally simulates the CMA experiment for the adversary:

1. Program a lazy random oracle, storing for each entry the hidden short preimage used to
   define that entry.
2. Answer signing queries using the sign-then-hash strategy: sample a short preimage
   `s` via `trapdoorSample`, compute `c = psf.eval pk s`, and program the RO at
   `(r, msg) := c`. Return `(r, s)` as the signature.
3. Run the adversary and, on a successful fresh forgery, return the simulator's hidden
   programmed preimage together with the forged preimage as a candidate collision.

The key insight is that in the sign-then-hash game, the reduction controls the entire
RO table. If the adversary forges on a fresh `(r*, msg*)` pair, the RO value at that
point was set by the reduction, so the hidden programmed preimage and the forged preimage
land at the same image under `psf.eval`.

The detailed construction simulates the adversary's oracle interactions by maintaining
a programmable RO state, using PSF correctness to ensure consistency. -/
noncomputable def reduction
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) :
    CollisionAdversary (PK := PK) (Domain := Domain) :=
  fun pk => do
    -- The simulation state threads the lazy random-oracle cache together with a *hidden
    -- preimage table* recording, for each programmed `(salt, message)` entry, the short
    -- preimage `s` used to define `psf.eval pk s` as the random-oracle value at that point.
    let State := (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)
    -- Random-oracle handler: on a cache hit reuse the recorded value; on a miss
    -- forward-sample a short preimage `s ← domainSample pk`, set the value to `psf.eval pk s`,
    -- and record `s` in the hidden table at the queried point.
    let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
      fun t => do
        let st ← get
        match st.1 t with
        | some v => pure v
        | none => do
            let s ← (domainSample pk : ProbComp Domain)
            let v := psf.eval pk s
            set ((st.1.cacheQuery t v, fun t' => if t' = t then some s else st.2 t') : State)
            pure v
    -- Uniform-sampling handler: answer uniform queries by drawing from the ambient `ProbComp`.
    let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
      fun t => (unifSpec.query t : ProbComp _)
    -- Signing handler (sign-then-hash): draw a fresh salt `r`, forward-sample a short preimage
    -- `s ← domainSample pk`, program the random oracle at `(r, msg) := psf.eval pk s`, record the
    -- hidden preimage, and return the signature `(r, s)`.
    let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
      fun msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let s ← (domainSample pk : ProbComp Domain)
        let v := psf.eval pk s
        let st ← get
        set ((st.1.cacheQuery (r, msg) v,
          fun t' => if t' = (r, msg) then some s else st.2 t') : State)
        pure (r, s)
    let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        (StateT State ProbComp) := (unifImpl + roImpl) + signImpl
    -- Run the adversary under the simulated oracle stack, then extract a collision candidate.
    let ((msgStar, (rStar, sStar)), st) ←
      (simulateQ impl (adv.main pk)).run (∅, fun _ => none)
    -- On the forgery `(msgStar, (rStar, sStar))`, look up the hidden programmed preimage at the
    -- forged point. If present, it and the forged preimage `sStar` share the image
    -- `psf.eval pk sStar` (the random-oracle value the reduction programmed there), forming a
    -- collision candidate. Otherwise fall back to the forged preimage itself.
    match st.2 (rStar, msgStar) with
    | some sHidden => pure (sHidden, sStar)
    | none => pure (sStar, sStar)

/-- The salt-collision birthday bound (GPV08, Proposition 6.2).

For `qSign` signing queries and `qHash` random-oracle queries, with salts drawn uniformly from a
set of size `|Salt|`, the standard GPV/FDH-with-salt bound on a fresh signing salt colliding with
any previously recorded random-oracle input (a prior signing salt or an adversary hash query) is
`(qSign + qHash)² / (2 · |Salt|)`. This upper-bounds the exact union sum
`qSign·(qSign-1)/2 + qSign·qHash` over the `qSign` fresh draws, each compared against at most
`j + qHash` recorded entries.

For Falcon with 40-byte salts (`|Salt| = 2^320`) and `qSign, qHash ≤ 2^64`:
  `collisionBound (Bytes 40) (2^64) (2^64) = 2^130 / (2 · 2^320) = 2^{-191}`. -/
noncomputable def collisionBound (qSign qHash : ℕ) : ENNReal :=
  ((qSign + qHash : ℕ) : ENNReal) ^ 2 / (2 * Fintype.card Salt)

open scoped Classical in
omit [DecidableEq Salt] in
/-- A single uniform salt draw lands in a fixed cache `cache ⊆ Salt` with probability exactly
`|cache| / |Salt|`.

This is the per-draw building block of the GPV salt-collision union bound: each fresh salt is
sampled uniformly and independently, so the chance it hits any of the previously recorded
random-oracle inputs is the size of that recorded set over the size of the salt space. -/
lemma probEvent_mem_uniformSample (cache : Finset Salt) :
    Pr[(· ∈ cache) | ($ᵗ Salt)] = cache.card / Fintype.card Salt := by
  rw [probEvent_uniformSample]
  congr 1
  simp

omit [DecidableEq Salt] [SampleableType Salt] in
/-- Arithmetic core of the GPV salt-collision birthday bound.

Summing the per-draw collision probabilities for `qSign` signing queries, where the `j`-th
fresh salt is compared against the at most `j + qHash` recorded random-oracle inputs (the `j`
prior signing salts and the up to `qHash` adversary hash queries), gives the running total
`∑_{j < qSign} (j + qHash) / |Salt|`. The exact sum
`∑_{j < qSign} (j + qHash) = qSign·(qSign-1)/2 + qSign·qHash` is at most `(qSign + qHash)² / 2`,
so the union bound is dominated by `collisionBound`. -/
lemma sum_range_div_card_le_collisionBound (qSign qHash : ℕ) :
    (∑ j ∈ Finset.range qSign, ((j + qHash : ℕ) : ℝ≥0∞) / Fintype.card Salt)
      ≤ collisionBound Salt qSign qHash := by
  unfold collisionBound
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hsum : (∑ j ∈ Finset.range qSign, ((j + qHash : ℕ) : ℝ≥0∞))
      = ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞) := by rw [Nat.cast_sum]
  rw [hsum]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc]
  gcongr
  have hnat : (∑ j ∈ Finset.range qSign, (j + qHash)) * 2 ≤ (qSign + qHash) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const, Finset.card_range,
      smul_eq_mul, add_mul, Nat.div_mul_cancel (Nat.even_mul_pred_self qSign).two_dvd]
    rcases Nat.eq_zero_or_pos qSign with h | h
    · simp [h]
    · nlinarith [Nat.sub_le qSign 1]
  have hcast : ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞) * 2
      ≤ (((qSign + qHash : ℕ) : ℝ≥0∞)) ^ 2 := by
    have h2 := (Nat.cast_le (α := ℝ≥0∞)).2 hnat
    push_cast at h2 ⊢
    convert h2 using 2
  calc ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞)
      = ((∑ j ∈ Finset.range qSign, (j + qHash) : ℕ) : ℝ≥0∞) * 2 * 2⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    _ ≤ ((qSign + qHash : ℕ) : ℝ≥0∞) ^ 2 * 2⁻¹ := by gcongr

open scoped Classical in
omit [DecidableEq Salt] in
/-- The GPV salt-collision union bound (GPV08, Proposition 6.2), as a uniform-draw-hits-cache
estimate.

If the random-oracle cache seen by the `j`-th signing query has size at most `j + qHash` (the `j`
prior signing salts plus the up to `qHash` adversary hash queries already recorded), then the
total probability that some fresh salt collides with a previously recorded entry is bounded by
`collisionBound`. The hypothesis `hcache` supplies the per-draw cache sizes `c j` together with
the bound `c j ≤ j + qHash`; the conclusion is the union bound over the `qSign` independent
uniform draws.

This is the real salt-collision event of the GPV proof (a fresh uniform draw hitting the
recorded random-oracle inputs), distinct from a hash-*output* collision over `|Range|`. -/
lemma probEvent_salt_collision_le_collisionBound (qSign qHash : ℕ)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash) :
    (∑ j ∈ Finset.range qSign, Pr[(· ∈ c j) | ($ᵗ Salt)]) ≤ collisionBound Salt qSign qHash := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_range_div_card_le_collisionBound Salt qSign qHash)
  intro j _
  rw [probEvent_mem_uniformSample]
  gcongr
  exact_mod_cast hcache j

/-! ## Salt-averaged collision telescope (the combined draw-then-query step)

A per-query `withProgramming` union framework cannot see the GPV salt averaging: the programming bad
flag fires deterministically on a *fixed* query input `t = (r, m)`, while the collision randomness
lives in the fresh salt `r` drawn *inside* the signing oracle, one step *before* the random-oracle
query is issued. The right granularity is therefore a **combined "draw salt `r`, then check `r`
against the recorded inputs" step**, whose firing probability, *integrated over the uniform salt
draw*, is `card cache / |Salt|`.

`saltSeq` is exactly this combined-step process abstracted away from the oracle plumbing: it
draws `qSign` fresh salts in sequence and reports whether any draw `r_j` lands in the recorded
set `c j` seen by the `j`-th signing query. `probEvent_saltSeq_le` telescopes the per-draw
collision probabilities (each a `probEvent_mem_uniformSample` instance) into the running sum
`∑_{j < qSign} card (c j) / |Salt|`, and `probEvent_saltSeq_le_collisionBound` finishes with the
Gauss-sum estimate `sum_range_div_card_le_collisionBound`. This is the salt-AVERAGED step bound
matching the granularity of the fresh salt draw. -/

open Classical in
omit [DecidableEq Salt] in
/-- The combined draw-then-collision-check process underlying the GPV salt-collision union bound.

`saltSeq c n` draws `n` fresh uniform salts in sequence; the `j`-th draw `r_j` is checked for
membership in the recorded random-oracle input set `c j` (the salts and hash inputs seen by the
`j`-th signing query). It returns `true` iff some draw collides with its recorded set. This is the
salt-averaged abstraction of "draw a fresh signing salt, then query the random oracle at it":
firing is integrated over the fresh draw rather than evaluated at a fixed query input. -/
noncomputable def saltSeq (c : ℕ → Finset Salt) : (n : ℕ) → ProbComp Bool
  | 0 => pure false
  | (n + 1) => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let rest ← saltSeq c n
      pure ((decide (r ∈ c n)) || rest)

/-- **Salt-averaged collision telescope.** The probability that the combined draw-then-check
process `saltSeq c n` ever reports a collision is bounded by the running sum of per-draw
collision probabilities `∑_{j < n} card (c j) / |Salt|`.

This is the salt-AVERAGED per-step bound: the head draw `r ← $ᵗ Salt` contributes
`card (c n) / |Salt|` (one `probEvent_mem_uniformSample` instance, integrated over the fresh salt),
and the remaining `n` draws contribute the inductive tail. The union is assembled by
`probEvent_bind_le_add` on the monotone Boolean disjunction. Unlike a fixed-`t` `withProgramming`
step (which fires deterministically and cannot be capped below `1`), every step here is averaged
over its own fresh salt draw, so the small `card / |Salt|` cap is honest. -/
theorem probEvent_saltSeq_le (c : ℕ → Finset Salt) (n : ℕ) :
    Pr[(· = true) | saltSeq (Salt := Salt) c n]
      ≤ ∑ j ∈ Finset.range n, ((c j).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) := by
  classical
  induction n with
  | zero => simp [saltSeq]
  | succ n ih =>
      rw [probEvent_congr' (q := fun y : Bool => ¬ y = false)
            (oa' := saltSeq (Salt := Salt) c (n + 1)) (fun b _ => by cases b <;> simp) rfl]
      rw [saltSeq, Finset.sum_range_succ, add_comm]
      refine probEvent_bind_le_add (m := ProbComp)
        (p := fun r => r ∉ c n) (q := fun b : Bool => b = false)
        (ε₁ := ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
        (ε₂ := ∑ j ∈ Finset.range n, ((c j).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
        ?_ ?_
      · simp only [not_not]
        rw [probEvent_uniformSample]
        simp
      · intro r _ hr
        simp only [Bool.not_eq_false]
        rw [decide_eq_false hr]
        simp only [Bool.false_or]
        rw [bind_pure]
        exact ih

/-- **Salt-averaged collision telescope, finished against `collisionBound`.** When the recorded
input set seen by the `j`-th signing query has size at most `j + qHash` (the `j` prior signing
salts plus the up to `qHash` adversary hash queries), the combined draw-then-check process over
`qSign` signing queries reports a collision with probability at most `collisionBound Salt qSign
qHash`.

This chains `probEvent_saltSeq_le` with the Gauss-sum estimate
`sum_range_div_card_le_collisionBound`. It is the salt-averaged collision bound stated directly on
the fresh-salt-draw process, the counterpart of the deterministic fixed-`t` step. -/
theorem probEvent_saltSeq_le_collisionBound (qSign qHash : ℕ)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash) :
    Pr[(· = true) | saltSeq (Salt := Salt) c qSign] ≤ collisionBound Salt qSign qHash := by
  refine (probEvent_saltSeq_le Salt c qSign).trans ?_
  refine le_trans (Finset.sum_le_sum ?_) (sum_range_div_card_le_collisionBound Salt qSign qHash)
  intro j _
  gcongr
  exact_mod_cast hcache j

open Classical in
/-- **Salt-split tsum identity.** Weighting the uniform-draw distribution by `1` on a finite cache
`s` and by a constant `q` off it sums to `p + (1 - p) · q`, where `p = card s / |Salt|` is the
probability of landing in `s`. This is the inclusion-exclusion kernel underlying both the
salt-collision recursion `probEvent_saltSeq_succ` and the per-step charge of the salt-inclusive
coupling induction `signRunF_tvDist_le_saltSeq`. -/
theorem tsum_probOutput_uniformSample_ite (s : Finset Salt) (q : ℝ≥0∞) :
    (∑' x : Salt, Pr[= x | ($ᵗ Salt : ProbComp Salt)] * (if x ∈ s then 1 else q))
      = ((s.card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
        + (1 - ((s.card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))) * q := by
  classical
  set p : ℝ≥0∞ := ((s.card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞)) with hp
  have hp_le : p ≤ 1 := by
    rw [hp, ← probEvent_mem_uniformSample (Salt := Salt) s]
    exact probEvent_le_one
  have hmem : Pr[(· ∈ s) | ($ᵗ Salt : ProbComp Salt)] = p := by
    rw [hp]; exact probEvent_mem_uniformSample (Salt := Salt) s
  have hcompl : Pr[(· ∉ s) | ($ᵗ Salt : ProbComp Salt)] = 1 - p := by
    have hsum := probEvent_compl (mx := ($ᵗ Salt : ProbComp Salt)) (· ∈ s)
    rw [hmem] at hsum
    have hbot : Pr[⊥ | ($ᵗ Salt : ProbComp Salt)] = 0 := by simp
    rw [hbot, tsub_zero] at hsum
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top hp_le) (by
      rw [add_comm]; exact hsum)
  have hsplit : ∀ x : Salt,
      Pr[= x | ($ᵗ Salt : ProbComp Salt)] * (if x ∈ s then 1 else q)
        = (if x ∈ s then Pr[= x | ($ᵗ Salt : ProbComp Salt)] else 0)
          + (if x ∈ s then 0 else Pr[= x | ($ᵗ Salt : ProbComp Salt)] * q) := by
    intro x; by_cases hx : x ∈ s <;> simp [hx]
  simp_rw [hsplit]
  rw [ENNReal.tsum_add]
  congr 1
  · rw [← probEvent_eq_tsum_ite]; exact hmem
  · have hre : ∀ x : Salt,
        (if x ∈ s then 0 else Pr[= x | ($ᵗ Salt : ProbComp Salt)] * q)
          = (if x ∉ s then Pr[= x | ($ᵗ Salt : ProbComp Salt)] else 0) * q := by
      intro x; by_cases hx : x ∈ s <;> simp [hx]
    simp_rw [hre]
    rw [ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite (p := (· ∉ s)), hcompl]

open Classical in
/-- **Exact one-step recursion of the salt-collision probability.** The probability that the
combined draw-then-check process `saltSeq c (n + 1)` reports a collision decomposes by independence
of the fresh head draw `r ← $ᵗ Salt` from the remaining `n` draws: with `p = card (c n) / |Salt|`
the head-collision probability, the head fires with probability `p`, and otherwise (probability
`1 - p`) the tail `saltSeq c n` must fire. Hence
`Pr[saltSeq c (n + 1)] = p + (1 - p) · Pr[saltSeq c n]`.

This is the tight inclusion-exclusion identity (the head draw and the tail are independent), the
per-step charge produced by the salt-inclusive coupling induction `signRunF_tvDist_le_saltSeq`. -/
theorem probEvent_saltSeq_succ (c : ℕ → Finset Salt) (n : ℕ) :
    Pr[(· = true) | saltSeq (Salt := Salt) c (n + 1)]
      = ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞)
        + (1 - ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞))
          * Pr[(· = true) | saltSeq (Salt := Salt) c n] := by
  classical
  set q : ℝ≥0∞ := Pr[(· = true) | saltSeq (Salt := Salt) c n] with hq
  -- Expand the head draw.
  conv_lhs => rw [saltSeq]
  rw [probEvent_bind_eq_tsum]
  -- Per-`r` inner probability: `1` if `r ∈ c n`, else `q`.
  have hinner : ∀ r : Salt,
      Pr[(· = true) | (saltSeq (Salt := Salt) c n >>=
            fun rest => (pure (decide (r ∈ c n) || rest) : ProbComp Bool))]
        = (if r ∈ c n then 1 else q) := by
    intro r
    by_cases hr : r ∈ c n
    · simp only [hr, if_true, decide_true, Bool.true_or]
      simp
    · simp only [hr, if_false, decide_false, Bool.false_or]
      rw [hq]
      simp
  simp_rw [hinner]
  exact tsum_probOutput_uniformSample_ite (Salt := Salt) (c n) q

/-! ## The salt-collision coupling and the hash-only granularity

The salt-averaged telescope above (`probEvent_saltSeq_le_collisionBound`) is the axiom-clean bound
on the GPV salt-collision event: a sequence of `qSign` fresh uniform salt draws, the `j`-th checked
against the recorded inputs `c j` of size `≤ j + qHash`, collides with probability at most
`collisionBound Salt qSign qHash`. This is the salt-AVERAGED combined "draw salt, then check" step
that a per-query `withProgramming` framework cannot express.

The U2 hypothesis `hbad` of `tvDist_runtime_real_programmed_le_collisionBound` cannot be supplied
from this telescope at that statement's granularity, for two independent structural reasons:

1. **Wrong event.** The `hbad` left-hand side is the `withProgramming` *bad flag*, which fires on a
   cache-*miss* whose query input lies in the programming policy's support
   (`cache t = none ∧ policy t = some v`; see `QueryImpl.withProgramming`). For the GPV simulator
   policy (which programs at every fresh signing point) this fires *deterministically* once an
   uncached signing point is reached, so its probability is near `1`, not `collisionBound`. The
   salt-collision event of the telescope is the opposite: a fresh salt *hitting* an
   already-recorded entry (a cache *hit* at a programmed point), which the monotone fire-on-miss
   flag does not record.

2. **Invisible salt draws.** `hbad` is phrased over `ob : OracleComp (Salt × M →ₒ Range)`, a
   random-oracle-only computation. The GPV signing salts are drawn in `unifSpec`/`ProbComp`, i.e.
   *outside* the `(Salt × M →ₒ Range)` spec, one step before each random-oracle query. By the time a
   query input `(r, m)` reaches the `withProgramming` handler the salt `r` is already a fixed value,
   so the `card / |Salt|` averaging that the telescope performs over the fresh draw is structurally
   absent from `ob`'s granularity.

The U2 *re-statement* `tvDist_runtime_real_programmed_le_collisionBound_saltInclusive` (below)
states U2 over the salt-inclusive signing run with the bad event instrumented as the cache-HIT salt
collision `saltSeq c qSign`, and discharges the loss-free `tvDist ≤ collisionBound.toReal`
conclusion *given* the up-to-bad coupling
`hcouple : tvDist(real, programmed) ≤ Pr[saltSeq c qSign = true]`. It does **not** route through the
fire-on-miss `hbad` (which, per reason 1 above, would require the false inequality
"fire-on-miss ≤ salt-collision").

The coupling `hcouple` is the identical-until-bad coupling between the real GPV run (lazy random
oracle, fresh uniform answer at each `(r, m)`) and the programmed run (answer `psf.eval pk s`),
whose only divergence is a fresh signing salt colliding with a recorded cache slice — precisely the
`saltSeq` event. It is a joint distribution over the interleaved `unifSpec` salt-draw /
`(Salt × M →ₒ Range)` random-oracle-query streams of the salt-inclusive signing program, and is
established below over the salt-inclusive vehicle `signRunF` — where the salt draws are explicit —
rather than at the hash-only `ob` interface where they are invisible (reason 2). -/

/-! ## Salt-inclusive identical-until-bad coupling primitives

The coupling is built on a *salt-inclusive* signing process `signRunF`, where the salt draws are
explicit and the salt-collision averaging is structurally visible. This section establishes the
identical-until-bad primitives for that process.

`tvDist_signStep_real_programmed_le_collision` is the per-step core: a single combined "draw a fresh
salt `r`, then answer" step, where the *real* branch answers with the lazy random-oracle value and
the *programmed* branch answers with the regularity-supplied value. Off the per-step salt collision
`r ∈ cache`, regularity makes the two answer branches agree in distribution (`h_eq`), so the
total-variation distance of the combined step is bounded by exactly the salt collision probability
`card cache / |Salt|`. This is the single-step instance of the fundamental-lemma-of-game-playing,
with the bad event averaged over the fresh salt draw. It specializes
`tvDist_bind_left_event_le`.

`signRunF` is the flag-carrying sequenced signing process: it draws `qSign` fresh salts in turn,
applies a per-step answer handler `step n state r`, and sets a Boolean flag the first time a drawn
salt lands in its recorded cache slice `c n`. Its flag-true marginal is the run-level counterpart of
the `saltSeq` collision event. `signRunF_flag_le_saltSeq` records that the flag-true probability of
the *real* run is bounded by `Pr[saltSeq c qSign = true]` (the flag fires iff some draw collides,
which is exactly the `saltSeq` disjunction marginalized over the threaded state).

`signRunF_tvDist_le_flag` is the multi-step coupling: the total-variation distance between the real
and programmed sequenced runs is bounded by the run-level flag-true probability. Off the per-step
collision the *current* step distributions agree (via `h_step`), but the two runs recurse with
*different* per-step handlers, so the off-bad agreement is threaded through the recursion with the
accumulating flag rather than obtained by a single application of the per-step primitive (the tails
differ). Chaining it with `signRunF_flag_le_saltSeq` and the telescope
`probEvent_saltSeq_le_collisionBound` yields the salt-inclusive coupling. -/

omit [DecidableEq Salt] [Fintype Salt] in
/-- **Per-step salt-inclusive identical-until-bad coupling.**

A single combined "draw a fresh salt `r`, then answer" step. The *real* answer branch `freal r` and
the *programmed* answer branch `fprog r` are coupled through the shared fresh salt draw. Off the
per-step salt collision `r ∈ cache`, regularity guarantees the two answer branches agree in
distribution (`h_eq`), so the total-variation distance of the combined step is bounded by the
probability that the fresh salt lands in `cache`, namely `card cache / |Salt|` (via
`probEvent_mem_uniformSample`).

This is the single-step instance of the fundamental-lemma-of-game-playing with the bad event
averaged over the fresh salt draw. It specializes `tvDist_bind_left_event_le` at
`mx := $ᵗ Salt` and `bad := (· ∈ cache)`. It is the per-step core the sequenced coupling
`signRunF_tvDist_le_flag` accumulates. -/
theorem tvDist_signStep_real_programmed_le_collision [Nonempty Salt] {β : Type}
    (cache : Finset Salt) (freal fprog : Salt → ProbComp β)
    (h_eq : ∀ r, r ∉ cache → 𝒟[freal r] = 𝒟[fprog r]) :
    tvDist
        (do let r ← ($ᵗ Salt : ProbComp Salt); freal r)
        (do let r ← ($ᵗ Salt : ProbComp Salt); fprog r)
      ≤ (Pr[(· ∈ cache) | ($ᵗ Salt : ProbComp Salt)]).toReal :=
  tvDist_bind_left_event_le _ freal fprog (· ∈ cache) h_eq

open Classical in
/-- **Flag-carrying sequenced signing process.**

`signRunF step c n` runs `n` combined signing steps over a threaded state `St × Bool`. At step `j`
it draws a fresh salt `r ← $ᵗ Salt`, advances the state by the per-step handler `step j state r`,
and records in the Boolean flag whether `r` landed in the recorded cache slice `c j`. The flag is
monotone (set once a collision occurs), so its final value is the run-level salt-collision event —
the salt-inclusive, state-threaded counterpart of the salt-averaged `saltSeq` process. -/
noncomputable def signRunF {St : Type} (step : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) : (n : ℕ) → St × Bool → ProbComp (St × Bool)
  | 0, sb => pure sb
  | (n + 1), sb => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let st' ← step n sb.1 r
      signRunF step c n (st', sb.2 || decide (r ∈ c n))

omit [Fintype Salt] in
/-- **`signRunF` never fails when its step never fails.** If every per-step handler `step n s r`
never fails, the whole `qSign`-step `signRunF` recursion never fails: the leading uniform salt draw
is total, the step is total by hypothesis, and the tail never fails by induction. Consequently its
output distribution has total mass one, so it can be discarded as a value-irrelevant never-failing
prefix (`evalDist_bind_const_neverFails`) — the tape-suffix-discard step of a fold factorization. -/
theorem signRunF_neverFail {St : Type} [Nonempty Salt]
    (step : ℕ → St → Salt → ProbComp St) (c : ℕ → Finset Salt)
    [hstep : ∀ n s r, NeverFail (step n s r)] :
    ∀ (n : ℕ) (sb : St × Bool), NeverFail (signRunF (Salt := Salt) step c n sb) := by
  intro n
  induction n with
  | zero => intro sb; exact inferInstanceAs (NeverFail (pure sb))
  | succ n ih =>
      intro sb
      refine (neverFail_bind_iff _ _).2 ⟨inferInstance, fun r _ => ?_⟩
      exact (neverFail_bind_iff _ _).2 ⟨hstep n sb.1 r, fun st' _ => ih _⟩

omit [Fintype Salt] in
/-- **Discarding the `signRunF` salt prefix.** When the per-step handler never fails, the entire
`signRunF` recursion never fails (`signRunF_neverFail`), so binding a *value-irrelevant*
continuation `k` after it contributes only `signRunF`'s total mass one: the salt-draw prefix is
discarded from the output distribution. This is the GPV `signRunF` instance of the generic
never-failing-prefix discard `evalDist_bind_const_neverFails`; it is the move that drops the
over-provisioned front salt tape once the genuine content has been spliced out, the analogue of the
`drawList` suffix discard in the worked Fiat–Shamir factorization. -/
theorem evalDist_signRunF_bind_const {St γ : Type} [Nonempty Salt]
    (step : ℕ → St → Salt → ProbComp St) (c : ℕ → Finset Salt)
    [∀ n s r, NeverFail (step n s r)] (n : ℕ) (sb : St × Bool) (k : ProbComp γ) :
    𝒟[signRunF (Salt := Salt) step c n sb >>= fun _ => k] = 𝒟[k] := by
  haveI := signRunF_neverFail (Salt := Salt) step c n sb
  refine SPMF.ext fun x => ?_
  set sr := signRunF (Salt := Salt) step c n sb with hsr
  rw [show 𝒟[sr >>= fun _ => k] x = Pr[= x | sr >>= fun _ => k] from (probOutput_def _ _).symm,
    show 𝒟[k] x = Pr[= x | k] from (probOutput_def _ _).symm,
    probOutput_bind_const, probFailure_eq_zero]
  simp

omit [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] in
/-- **Uniform per-fibre TV bound for a shared base.** If two continuations are pointwise at
total-variation distance at most `δ` (with `δ ≥ 0`), then binding them over a common base
computation is also within `δ`. The base only needs to be a sub-probability computation; the mass
`∑' Pr[= a] ≤ 1` absorbs the constant fibre bound. -/
theorem tvDist_bind_le_of_forall_le {α β : Type} (mx : ProbComp α) (f g : α → ProbComp β)
    (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ a, tvDist (f a) (g a) ≤ δ) :
    tvDist (mx >>= f) (mx >>= g) ≤ δ := by
  refine le_trans (tvDist_bind_left_le mx f g) ?_
  have hbase : Summable (fun a : α => Pr[= a | mx].toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
  have hsum_le_one : ∑' a : α, Pr[= a | mx].toReal ≤ 1 := by
    have h1 : (∑' a : α, Pr[= a | mx].toReal) = (∑' a : α, Pr[= a | mx]).toReal :=
      (ENNReal.tsum_toReal_eq (fun a => ne_top_of_le_ne_top one_ne_top probOutput_le_one)).symm
    rw [h1, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
      one_ne_top).2 tsum_probOutput_le_one
  calc ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a)
        ≤ ∑' a, Pr[= a | mx].toReal * δ :=
        Summable.tsum_le_tsum
          (fun a => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
          (Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
            (fun a => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg) (hbase.mul_right δ))
          (hbase.mul_right δ)
    _ = (∑' a, Pr[= a | mx].toReal) * δ := by rw [tsum_mul_right]
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hsum_le_one hδ
    _ = δ := one_mul δ

open Classical in
omit [Fintype Salt] in
/-- **Stateful identical-until-bad telescoping (generalized over the initial flag and state).**

This is the inductive heart of the salt-inclusive coupling. For any initial flag `b` and state
`st`, the total-variation distance between the real and programmed sequenced runs is bounded by the
salt-averaged collision probability `Pr[saltSeq c n = true]`, *independently of `b` and `st`* (the
flag only accumulates the collision disjunction and the RHS does not depend on the threaded state).

The successor step shares the fresh salt draw `r ← $ᵗ Salt` and splits per-`r`:
* On the per-step collision `r ∈ c n` the step is charged its full mass (`tvDist ≤ 1`), contributing
  the head term `card (c n) / |Salt|`.
* Off the collision (`r ∉ c n`) the head handlers agree in distribution (`h_step`), so by the
  triangle inequality the step contributes only the tail, bounded by the induction hypothesis at the
  advanced state and flag. The `NeverFail` hypothesis keeps the state-marginal mass equal to one.

The per-`r` charges accumulate to exactly `card (c n) / |Salt| + (1 - card (c n) / |Salt|) ·
Pr[saltSeq c n]`, which equals `Pr[saltSeq c (n + 1)]` by the independence identity
`probEvent_saltSeq_succ`. This realizes design L3a: a stateful telescoping accepting
state-dependent per-step costs. -/
theorem signRunF_tvDist_le_saltSeq_aux {St : Type} [Finite Salt]
    (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) [∀ n st r, NeverFail (stepReal n st r)]
    (h_step : ∀ n st r, r ∉ c n → 𝒟[stepReal n st r] = 𝒟[stepProg n st r])
    (n : ℕ) (st : St) (b : Bool) :
    tvDist (signRunF (Salt := Salt) stepReal c n (st, b))
        (signRunF (Salt := Salt) stepProg c n (st, b))
      ≤ (Pr[(· = true) | saltSeq (Salt := Salt) c n]).toReal := by
  classical
  haveI : Fintype Salt := Fintype.ofFinite Salt
  induction n generalizing st b with
  | zero =>
      simp only [signRunF]
      rw [tvDist_self]
      exact ENNReal.toReal_nonneg
  | succ n ih =>
      -- Notation for the per-step head-collision probability `p` and tail probability `q`.
      set q : ℝ≥0∞ := Pr[(· = true) | saltSeq (Salt := Salt) c n] with hq
      set p : ℝ≥0∞ := ((c n).card : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) with hp
      have hp_le : p ≤ 1 := by
        rw [hp, ← probEvent_mem_uniformSample (Salt := Salt) (c n)]
        exact probEvent_le_one
      have hq_le : q ≤ 1 := by rw [hq]; exact probEvent_le_one
      -- Unfold one step on both sides; the salt draw `r ← $ᵗ Salt` is shared.
      rw [signRunF, signRunF]
      -- Per-`r` continuation bound.
      refine le_trans (tvDist_bind_left_le ($ᵗ Salt : ProbComp Salt) _ _) ?_
      -- Bound each per-`r` term by `if r ∈ c n then 1 else q.toReal`.
      have hterm : ∀ r : Salt,
          tvDist (stepReal n st r >>= fun st' =>
              signRunF (Salt := Salt) stepReal c n (st', b || decide (r ∈ c n)))
            (stepProg n st r >>= fun st' =>
              signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
            ≤ (if r ∈ c n then 1 else q.toReal) := by
        intro r
        by_cases hr : r ∈ c n
        · rw [if_pos hr]; exact tvDist_le_one _ _
        · rw [if_neg hr]
          -- Triangle through the real head with the programmed tail.
          refine le_trans (tvDist_triangle _
            (stepReal n st r >>= fun st' =>
              signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n))) _) ?_
          have htail : tvDist (stepReal n st r >>= fun st' =>
                signRunF (Salt := Salt) stepReal c n (st', b || decide (r ∈ c n)))
              (stepReal n st r >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
              ≤ q.toReal :=
            tvDist_bind_le_of_forall_le (stepReal n st r) _ _ q.toReal ENNReal.toReal_nonneg
              (fun st' => ih st' (b || decide (r ∈ c n)))
          have hhead : tvDist (stepReal n st r >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
              (stepProg n st r >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (r ∈ c n)))
              = 0 := by
            rw [tvDist_eq_zero_iff, evalDist_bind, evalDist_bind, h_step n st r hr]
          rw [hhead, add_zero]
          exact htail
      -- Normalize the product projections `(st, b).1`, `(st, b).2` to `st`, `b`.
      change (∑' a : Salt, Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal *
          tvDist (stepReal n st a >>= fun st' =>
              signRunF (Salt := Salt) stepReal c n (st', b || decide (a ∈ c n)))
            (stepProg n st a >>= fun st' =>
              signRunF (Salt := Salt) stepProg c n (st', b || decide (a ∈ c n))))
        ≤ (Pr[(· = true) | saltSeq (Salt := Salt) c (n + 1)]).toReal
      -- `q.toReal ≤ 1` and base summability.
      have hq_toReal_le : q.toReal ≤ 1 := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_le_toReal probEvent_ne_top one_ne_top).2 hq_le
      have hbase : Summable (fun a : Salt => Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal) :=
        ENNReal.summable_toReal (ne_top_of_le_ne_top one_ne_top tsum_probOutput_le_one)
      have hcap : ∀ a : Salt, (if a ∈ c n then (1 : ℝ) else q.toReal) ≤ 1 := by
        intro a; split_ifs with ha
        · exact le_refl 1
        · exact hq_toReal_le
      have hcap_nonneg : ∀ a : Salt, (0 : ℝ) ≤ (if a ∈ c n then (1 : ℝ) else q.toReal) := by
        intro a; split_ifs <;> [norm_num; exact ENNReal.toReal_nonneg]
      -- Summability of the salt-split bounding sum.
      have hsummable_term : Summable (fun a : Salt =>
          Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal * (if a ∈ c n then 1 else q.toReal)) :=
        Summable.of_nonneg_of_le
          (fun a => mul_nonneg ENNReal.toReal_nonneg (hcap_nonneg a))
          (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (hcap a)) hbase
      -- Summability of the actual tvDist-weighted sum.
      have hsummable_tv : Summable (fun a : Salt =>
          Pr[= a | ($ᵗ Salt : ProbComp Salt)].toReal *
            tvDist (stepReal n st a >>= fun st' =>
                signRunF (Salt := Salt) stepReal c n (st', b || decide (a ∈ c n)))
              (stepProg n st a >>= fun st' =>
                signRunF (Salt := Salt) stepProg c n (st', b || decide (a ∈ c n)))) :=
        Summable.of_nonneg_of_le
          (fun a => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
          (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg
            ((hterm a).trans (hcap a))) hbase
      refine le_trans (Summable.tsum_le_tsum (fun a =>
        mul_le_mul_of_nonneg_left (hterm a) ENNReal.toReal_nonneg)
        hsummable_tv hsummable_term) ?_
      -- Identify the salt-split sum with `Pr[saltSeq c (n+1)].toReal`.
      -- Each real term is the `toReal` of the corresponding `ℝ≥0∞` term.
      have hterm_toReal : ∀ i : Salt,
          Pr[= i | ($ᵗ Salt : ProbComp Salt)].toReal * (if i ∈ c n then (1 : ℝ) else q.toReal)
            = (Pr[= i | ($ᵗ Salt : ProbComp Salt)] * (if i ∈ c n then 1 else q)).toReal := by
        intro i
        by_cases hi : i ∈ c n <;> simp [hi]
      simp_rw [hterm_toReal]
      -- Pull the `toReal` out of the sum (each term is finite), evaluate, and identify.
      rw [← ENNReal.tsum_toReal_eq (fun i => ENNReal.mul_ne_top
        (ne_top_of_le_ne_top one_ne_top probOutput_le_one) (by
          split_ifs <;> [exact one_ne_top; exact probEvent_ne_top])),
        tsum_probOutput_uniformSample_ite (Salt := Salt) (c n) q, ← probEvent_saltSeq_succ]

omit [Fintype Salt] in
/-- **Salt-inclusive identical-until-bad coupling.**

The total-variation distance between the real sequenced signing run `signRunF stepReal c n` and the
programmed sequenced signing run `signRunF stepProg c n` is bounded by the salt-averaged collision
probability `Pr[saltSeq c n = true]`, provided the two per-step handlers agree in distribution off
the per-step salt collision `r ∈ c j` (`h_step`, supplied for GPV by regularity `hreg`). The
`NeverFail` hypothesis on the real handler keeps probability mass during the state marginalization.

This is the multi-step joint coupling, threaded through the recursion by
`signRunF_tvDist_le_saltSeq_aux` (the generalization over the initial flag and state). It decomposes
into two parts:

* **Per-step charge.** Off `r ∈ c j` the two combined "draw salt, then answer" steps agree in
  distribution, so each step contributes only its salt-collision mass `card (c j) / |Salt|`. This is
  the per-step primitive `tvDist_signStep_real_programmed_le_collision`, applied per fibre
  via `tvDist_bind_le_of_forall_le`.
* **Accumulation to `saltSeq`.** The per-step charges accumulate along the recursion to the
  run-level collision-flag probability, which equals the salt-averaged `saltSeq` disjunction once
  the threaded state is marginalized out — the inclusion-exclusion identity
  `probEvent_saltSeq_succ`.

Chaining this result with the telescope `probEvent_saltSeq_le_collisionBound`
(`Pr[saltSeq] ≤ collisionBound`) yields the salt-inclusive coupling that discharges the U2
hypothesis `hcouple`, once the GPV reduction handlers and per-step caches `c j` are instantiated. -/
theorem signRunF_tvDist_le_saltSeq {St : Type} [Finite Salt]
    (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) [∀ n st r, NeverFail (stepReal n st r)]
    (h_step : ∀ n st r, r ∉ c n → 𝒟[stepReal n st r] = 𝒟[stepProg n st r])
    (n : ℕ) (st : St) :
    tvDist (signRunF (Salt := Salt) stepReal c n (st, false))
        (signRunF (Salt := Salt) stepProg c n (st, false))
      ≤ (Pr[(· = true) | saltSeq (Salt := Salt) c n]).toReal :=
  signRunF_tvDist_le_saltSeq_aux (Salt := Salt) (St := St)
    stepReal stepProg c h_step n st false

/-- **U2, re-stated over the salt-inclusive signing run (unconditional).**

This is the salt-inclusive U2: it bounds the total-variation distance between the real and
programmed *signing runs* directly by `collisionBound`, with **no coupling hypothesis**. Unlike the
hash-only `tvDist_runtime_real_programmed_le_collisionBound_saltInclusive` (which takes the coupling
as the typed hypothesis `hcouple`), this lemma is phrased over the salt-inclusive vehicle
`signRunF` — where each of the `qSign` fresh signing salts `r ← $ᵗ Salt` is an explicit step of the
recursion — so the salt-collision averaging is *structurally visible* and the coupling discharges it
outright.

The proof chains two results with no loss:
* the multi-step coupling `signRunF_tvDist_le_saltSeq`
  (`tvDist (signRunF stepReal …) (signRunF stepProg …) ≤ Pr[saltSeq c qSign = true]`), and
* the salt-averaged telescope `probEvent_saltSeq_le_collisionBound`
  (`Pr[saltSeq c qSign = true] ≤ collisionBound Salt qSign qHash`),
moved to `ℝ` by `ENNReal.toReal_mono` (using `collisionBound < ⊤`).

`stepReal`/`stepProg` are the per-signing-step answer handlers (real lazy random oracle vs the
regularity-supplied programmed answer); `h_step` is the off-collision branch agreement supplied by
PSF regularity (`psf.Regularity`); `c j` is the recorded random-oracle cache slice seen by the
`j`-th signing query, with the standard growth bound `card (c j) ≤ j + qHash` (`hcache`).

Feeding the four GPV theorems additionally requires the adaptive→`signRunF` factorization: matching
the real adversary run `simulateQ impl (adv.main pk)` — which interleaves the `qSign` signing
queries (each drawing a fresh salt) with up to `qHash` adversary hash queries *adaptively* — to this
fixed `qSign`-step `signRunF` recursion. That factorization is the deferred-sampling joint coupling
packaged as `AdaptiveFactorizesSignRunF` (see the *Adaptive→signRunF factorization* section
below). -/
theorem signRunF_tvDist_le_collisionBound {St : Type} [Finite Salt] [Nonempty Salt]
    (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) [∀ n st r, NeverFail (stepReal n st r)]
    (h_step : ∀ n st r, r ∉ c n → 𝒟[stepReal n st r] = 𝒟[stepProg n st r])
    (qSign qHash : ℕ) (hcache : ∀ j, (c j).card ≤ j + qHash) (st : St) :
    tvDist (signRunF (Salt := Salt) stepReal c qSign (st, false))
        (signRunF (Salt := Salt) stepProg c qSign (st, false))
      ≤ (collisionBound Salt qSign qHash).toReal := by
  refine (signRunF_tvDist_le_saltSeq (Salt := Salt) stepReal stepProg c h_step qSign st).trans ?_
  refine ENNReal.toReal_mono ?_ (probEvent_saltSeq_le_collisionBound Salt qSign qHash c hcache)
  refine (ENNReal.div_lt_top ?_ ?_).ne
  · simp
  · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
    exact Fintype.card_ne_zero

/-! ## Adaptive→`signRunF` factorization

The unconditional salt-inclusive U2 `signRunF_tvDist_le_collisionBound` (above) bounds the real and
programmed *salt-inclusive signing runs* — phrased over the fixed `qSign`-step recursion `signRunF`.
To consume it in the four GPV theorems, whose advantage is over the **adaptive** real game run
`simulateQ impl (adv.main pk)` (`SignatureAlg.unforgeableExp`), one must match that adaptive run to
the fixed `signRunF` recursion. That match is the **adaptive→`signRunF` factorization**:
the adversary interleaves its `≤ qSign` signing queries (each drawing one fresh salt `r ← $ᵗ Salt`)
with `≤ qHash` random-oracle queries *adaptively*, while `signRunF` draws its `qSign` salts in a
fixed front sequence. Front-loading the interleaved salt draws past the adaptive adversary fold is a
deferred-sampling joint coupling, structurally identical to the Fiat–Shamir-with-abort
*fold-level tape factorization*
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead` (each signing body's inline
draws are recast as consumption from a pre-drawn front tape, proved by induction over the
`simulateQ` fold using `OracleComp.DeferredSampling.evalDist_step_commute_tape` for the
answer-irrelevant — here, the adversary hash/uniform — steps and a per-body splice for the drawing
steps).

This section establishes the off-collision branch agreement and packages the factorization as a
typed predicate.

* `regularity_signAnswer_agree` discharges the abstract coupling's off-collision branch-agreement
  hypothesis (`h_step`) for the concrete GPV signing answer: under PSF regularity the *real*
  RO-cache-miss answer `(c, s)` (fresh uniform target `c ← $ᵗ Range`, then
  `s ← trapdoorSample pk sk c`) and the *programmed* answer (`s ← domainSample pk`, target
  `eval pk s`) are equal in distribution. This is the regularity equation transposed and is the
  per-step content the off-collision case of `signRunF_tvDist_le_saltSeq_aux` consumes.

* `AdaptiveFactorizesSignRunF` is the typed predicate packaging the factorization — that the
  adaptive real and programmed game runs are distributed as the corresponding `signRunF` runs over a
  common per-query cache sequence `c` with `card (c j) ≤ j + qHash`. It is a `Prop` (a typed
  obligation, in the style of `hcouple`), naming the deferred-sampling content as a single target.
  `factorized_advantage_le_collisionBound` shows that supplying it discharges the salt-inclusive U2
  against the adaptive game run via the unconditional `signRunF_tvDist_le_collisionBound`. -/

omit [DecidableEq Range] in
/-- **Regularity branch-agreement bridge.** Under PSF regularity, the real cache-miss
signing answer and the programmed signing answer agree in distribution.

The real answer at a fresh salt — produced by the lazy random oracle on a cache miss — draws a fresh
uniform target `c ← $ᵗ Range` and then a short preimage `s ← trapdoorSample pk sk c`, returning the
pair `(c, s)`. The programmed answer draws `s ← domainSample pk` and uses the target `eval pk s`,
returning `(eval pk s, s)`. PSF regularity (`psf.Regularity`) states exactly that these two joint
distributions coincide, so this is the regularity equation read right-to-left.

This is the GPV-concrete witness for the off-collision branch-agreement hypothesis `h_step` of
`signRunF_tvDist_le_saltSeq` / `signRunF_tvDist_le_collisionBound`: off the per-step salt collision
`r ∉ c j`, the real and programmed per-signing-step answer handlers agree in distribution. -/
theorem regularity_signAnswer_agree (hreg : psf.Regularity) (pk : PK) (sk : SK) :
    ∃ domainSample : PK → ProbComp Domain,
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
          : ProbComp (Range × Domain))]
        = 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨domainSample, (h pk sk).symm⟩

/-- **Adaptive→`signRunF` factorization predicate.**

`AdaptiveFactorizesSignRunF realRun progRun` asserts the existence of a `signRunF` presentation of
the adaptive real and programmed game runs sharing a common per-signing-query cache sequence: there
exist a handler-state type `St`, real/programmed per-step answer handlers `stepReal`/`stepProg` (the
latter agreeing with the former off the per-step salt collision, `stepReal` never failing), a
per-query recorded-cache sequence `c` bounded by `card (c j) ≤ j + qHash`, and a start state such
that the real and programmed adaptive runs equal (in distribution) the corresponding
`signRunF stepReal c qSign` / `signRunF stepProg c qSign` runs.

This is the content the deferred-sampling fold-level coupling establishes (cf.
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`): front-load the
adaptively-interleaved fresh salt draws of `realRun`/`progRun` into the fixed `qSign`-step
`signRunF` sequence. It is a typed predicate naming the factorization as a single target;
`factorized_advantage_le_collisionBound` shows it suffices. -/
def AdaptiveFactorizesSignRunF [Nonempty Salt] {α : Type}
    (realRun progRun : SPMF α) (qSign qHash : ℕ) : Prop :=
  ∃ (St : Type) (stepReal stepProg : ℕ → St → Salt → ProbComp St)
    (c : ℕ → Finset Salt) (st : St) (g : St × Bool → ProbComp α),
    (∀ n s r, NeverFail (stepReal n s r)) ∧
    (∀ n s r, r ∉ c n → 𝒟[stepReal n s r] = 𝒟[stepProg n s r]) ∧
    (∀ j, (c j).card ≤ j + qHash) ∧
    realRun = 𝒟[signRunF (Salt := Salt) stepReal c qSign (st, false) >>= g] ∧
    progRun = 𝒟[signRunF (Salt := Salt) stepProg c qSign (st, false) >>= g]

/-- **The factorization predicate suffices.** Supplying the adaptive→`signRunF` factorization
predicate `AdaptiveFactorizesSignRunF` discharges the salt-inclusive U2 against the adaptive game
runs: the total-variation distance between the real and programmed game runs is bounded by
`collisionBound Salt qSign qHash`.

The proof factors the runs through the predicate's `signRunF` presentation, applies the
data-processing inequality `tvDist_bind_right_le` to drop the shared post-processing `g`, and closes
with the unconditional salt-inclusive U2 `signRunF_tvDist_le_collisionBound`. Once the
deferred-sampling fold-level coupling establishes `AdaptiveFactorizesSignRunF`, the four GPV
theorems' sign-then-hash hop follows with no further probability content. -/
theorem factorized_advantage_le_collisionBound [Finite Salt] [Nonempty Salt] {α : Type}
    (realRun progRun : SPMF α) (qSign qHash : ℕ)
    (hfac : AdaptiveFactorizesSignRunF (Salt := Salt) realRun progRun qSign qHash) :
    SPMF.tvDist realRun progRun ≤ (collisionBound Salt qSign qHash).toReal := by
  obtain ⟨St, stepReal, stepProg, c, st, g, hNF, hstep, hcache, hreal, hprog⟩ := hfac
  subst hreal hprog
  refine le_trans (tvDist_bind_right_le g _ _) ?_
  haveI : ∀ n s r, NeverFail (stepReal n s r) := hNF
  exact signRunF_tvDist_le_collisionBound (Salt := Salt) (St := St)
    stepReal stepProg c hstep qSign qHash hcache st

/-! ## Concrete GPV `signRunF` handlers

The predicate `AdaptiveFactorizesSignRunF` is an existential over a handler-state type `St`,
real/programmed per-step handlers, a recorded-cache sequence `c`, a start state, and a shared
post-processor `g`. This section pins the GPV-concrete witnesses for the handler-state and step
handlers, and proves the two *structural* conjuncts of the predicate against them — the `NeverFail`
of the real step and the off-collision branch agreement under regularity. The two run-equalities
`realRun = 𝒟[signRunF stepReal c qSign …]` / `progRun = 𝒟[signRunF stepProg c qSign …]` together
with the cache-growth bound on the *adaptive* run's recorded slices are the front-loading fold
factorization, established via `gpv_tvDist_tape_runs_le_collisionBound` below.

The handler state is the lazy random-oracle cache `(Salt × M →ₒ Range).QueryCache`; both step
handlers update it at the freshly drawn salt `r` and the `n`-th signing message `msgs n`. The
`stepReal` handler mirrors the real signing oracle's *cache-miss* branch: draw a uniform target
`c ← $ᵗ Range`, draw the trapdoor preimage, and cache `c`. The `stepProg` handler mirrors the
sign-then-hash simulator: forward-sample a short preimage `s ← domainSample pk` and program the
cache entry to `psf.eval pk s`. -/

open Classical in
/-- **Real GPV signing step (cache-miss branch).** At signing step `n` with random-oracle cache
`cache` and freshly drawn salt `r`, draw a uniform target `c ← $ᵗ Range`, draw a trapdoor preimage
of `c`, and record `(r, msgs n) ↦ c` in the cache. This is the per-step handler used as `stepReal`
in the GPV `signRunF` presentation of the real game run. -/
noncomputable def gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) :
    ℕ → (Salt × M →ₒ Range).QueryCache → Salt → ProbComp ((Salt × M →ₒ Range).QueryCache) :=
  fun n cache r => do
    let c ← ($ᵗ Range)
    let _s ← psf.trapdoorSample pk sk c
    pure (cache.cacheQuery (r, msgs n) c)

open Classical in
/-- **Programmed GPV signing step (sign-then-hash branch).** At signing step `n` with random-oracle
cache `cache` and freshly drawn salt `r`, forward-sample a short preimage `s ← domainSample pk` and
record `(r, msgs n) ↦ psf.eval pk s` in the cache. This is the per-step handler used as `stepProg`
in the GPV `signRunF` presentation of the programmed (simulator) run. -/
noncomputable def gpvStepProg (pk : PK) (domainSample : PK → ProbComp Domain) (msgs : ℕ → M) :
    ℕ → (Salt × M →ₒ Range).QueryCache → Salt → ProbComp ((Salt × M →ₒ Range).QueryCache) :=
  fun n cache r => do
    let s ← domainSample pk
    pure (cache.cacheQuery (r, msgs n) (psf.eval pk s))

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real GPV step never fails.** Given that the trapdoor sampler never fails (a mild
side-condition satisfied by any total preimage sampler — e.g. Falcon's `ffSampling` loop, which
always returns), the real per-step handler `gpvStepReal` never fails: the uniform target draw is
total, the trapdoor draw is total by hypothesis, and the final cache update is a `pure`. This
discharges the `NeverFail (stepReal n s r)` conjunct of the obligation against the concrete
`stepReal := gpvStepReal`. -/
theorem gpvStepReal_neverFail (pk : PK) (sk : SK) (msgs : ℕ → M)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (n : ℕ) (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) :
    NeverFail (gpvStepReal psf M Salt pk sk msgs n cache r) := by
  unfold gpvStepReal
  rw [neverFail_bind_iff]
  refine ⟨inferInstance, fun c _ => ?_⟩
  rw [neverFail_bind_iff]
  exact ⟨hNF c, fun _ _ => inferInstance⟩

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real/programmed GPV step distributional agreement.** Under PSF regularity (witnessed by the
forward sampler `domainSample` of `psf.Regularity`), the real and programmed per-step handlers agree
as output distributions at every step `n`, cache, and salt `r`.

Both handlers update the same cache slot `(r, msgs n)` with the first component of a `(target,
preimage)` pair; the real handler draws that pair as `(c, s)` with `c ← $ᵗ Range`, `s ←
trapdoorSample pk sk c`, while the programmed handler draws it as `(eval pk s, s)` with `s ←
domainSample pk`. PSF regularity equates exactly these two joint distributions, so projecting onto
the cache update preserves the equality. This agreement is in fact *unconditional* in `r` (it does
not require `r ∉ c n`), which is stronger than the obligation's off-collision conjunct demands. -/
theorem gpvStep_agree (pk : PK) (sk : SK) (msgs : ℕ → M)
    (domainSample : PK → ProbComp Domain)
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (n : ℕ) (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) :
    𝒟[gpvStepReal psf M Salt pk sk msgs n cache r]
      = 𝒟[gpvStepProg psf M Salt pk domainSample msgs n cache r] := by
  unfold gpvStepReal gpvStepProg
  set proj : Range × Domain → (Salt × M →ₒ Range).QueryCache :=
    fun cs => cache.cacheQuery (r, msgs n) cs.1 with hproj
  have hR : (($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>=
              fun _s => (pure (cache.cacheQuery (r, msgs n) c) : ProbComp _))
        = ((($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>= fun s => pure (c, s)) >>=
            fun cs => pure (proj cs)) := by simp [hproj]
  have hP : (domainSample pk >>=
              fun s => (pure (cache.cacheQuery (r, msgs n) (psf.eval pk s)) : ProbComp _))
        = ((domainSample pk >>= fun s => pure (psf.eval pk s, s)) >>=
            fun cs => pure (proj cs)) := by simp [hproj]
  change 𝒟[(($ᵗ Range) >>= fun c => psf.trapdoorSample pk sk c >>=
              fun _s => pure (cache.cacheQuery (r, msgs n) c))] = _
  rw [hR, hP]
  simp only [evalDist_bind, hreg]

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Real GPV signing-body cache splice (cache-miss key).** One real signing-query body, run
through the lazy random oracle at a *missing* cache key `(r, msgs n)`, produces a recorded-cache
transition distributed exactly as the concrete `signRunF` real step `gpvStepReal` at the (already
fixed) salt `r`.

The signing body queries the random oracle at `(r, msgs n)`; on the cache miss `cache (r, msgs n) =
none` the oracle draws a fresh uniform target `u ← $ᵗ Range`, records `(r, msgs n) ↦ u`, and returns
`u`; the body then draws the trapdoor preimage and yields the updated cache. The handler
`gpvStepReal` draws the same uniform target `c ← $ᵗ Range`, the same trapdoor preimage, and records
`(r, msgs n) ↦ c` — so the two recorded-cache distributions coincide. This is the *per-body splice*
of the adaptive→`signRunF` fold factorization (the signing-step case of
`gpv_tvDist_tape_runs_le_collisionBound`): it recasts one inline signing-oracle body, on a
fresh-salt cache miss, as the concrete `signRunF` real step, with the fresh salt `r` front-loaded
out of the body. It is *pinned* to the concrete `randomOracle` and `gpvStepReal`, requires only the
cache-miss side condition `hmiss` (guaranteed for a fresh salt), and is unconditional otherwise. -/
theorem evalDist_gpvSignBody_run_eq_gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) (n : ℕ)
    (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt)
    (hmiss : cache (r, msgs n) = none) :
    𝒟[(do
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msgs n)).run cache
        let _s ← psf.trapdoorSample pk sk p.1
        pure p.2 : ProbComp ((Salt × M →ₒ Range).QueryCache))]
      = 𝒟[gpvStepReal psf M Salt pk sk msgs n cache r] := by
  unfold gpvStepReal
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) (r, msgs n)).run cache
        = (fun u => (u, cache.cacheQuery (r, msgs n) u)) <$>
            (uniformSampleImpl (spec := (Salt × M →ₒ Range)) (r, msgs n))
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  rw [show (uniformSampleImpl (spec := (Salt × M →ₒ Range)) (r, msgs n))
        = ($ᵗ Range : ProbComp Range) from rfl]
  rw [map_eq_bind_pure_comp, bind_assoc]
  simp only [Function.comp_apply, pure_bind]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Programmed GPV signing-body cache splice (simulator signing query).** One programmed
simulator signing-query body — the `signImpl` handler of `progGameRun`, which draws a fresh salt
`r ← $ᵗ Salt`, forward-samples a short preimage `s ← domainSample pk`, programs the random-oracle
cache entry `(r, msg) ↦ psf.eval pk s`, updates the preimage record, and returns `(r, s)` — has its
recorded random-oracle *cache component* (with the salt draw front-loaded, and the returned
signature and the auxiliary preimage record dropped) distributed exactly as the salt-prefixed
concrete `signRunF` programmed step: draw the same fresh salt `r ← $ᵗ Salt`, then apply
`gpvStepProg` at that `r`.

This is the programmed-side dual of `evalDist_gpvSignBody_run_eq_gpvStepReal`, and the signing-step
case of the *programmed* run-equality
`progGameRun … = 𝒟[signRunF gpvStepProg c qSign …]` underlying
`gpv_tvDist_tape_runs_le_collisionBound`. It is *pinned* to the concrete `progGameRun` signing body
and the concrete `gpvStepProg`: the cache transition
`cache ↦ cache.cacheQuery (r, msgs n) (psf.eval pk s)`
on both sides is the same, the salt draw is the same front-loaded `$ᵗ Salt`, and `domainSample` is
the shared programming randomness. No probability-mass averaging is performed; the equality is the
exact recasting of one inline simulator signing body — with its salt front-loaded — as one
`signRunF` programmed step. The auxiliary preimage record `((Salt × M) → Option Domain)` of
`progGameRun`'s state, which `gpvStepProg` does not carry, is dropped here (it is
collision-extraction bookkeeping, irrelevant to the random-oracle cache distribution that the
sign-then-hash hop compares; it is reattached at the run level, not the per-step level). -/
theorem evalDist_gpvSignBody_run_eq_gpvStepProg (pk : PK) (domainSample : PK → ProbComp Domain)
    (msgs : ℕ → M) (n : ℕ)
    (cache : (Salt × M →ₒ Range).QueryCache) (pre : (Salt × M) → Option Domain) :
    𝒟[(do
        -- The actual `progGameRun` simulator signing body (`signImpl`), with the fresh salt draw
        -- front-loaded, run on state `(cache, pre)`; project out the random-oracle cache component
        -- (dropping the returned signature and the auxiliary preimage record).
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← ((do
            let s ← (domainSample pk : ProbComp Domain)
            let v := psf.eval pk s
            let st ← get
            set ((st.1.cacheQuery (r, msgs n) v,
              fun t' => if t' = (r, msgs n) then some s else st.2 t')
                : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain))
            pure (r, s) :
              StateT ((Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain))
                ProbComp (Salt × Domain)).run (cache, pre))
        pure p.2.1 : ProbComp ((Salt × M →ₒ Range).QueryCache))]
      = 𝒟[(do
          let r ← ($ᵗ Salt : ProbComp Salt)
          gpvStepProg psf M Salt pk domainSample msgs n cache r
            : ProbComp ((Salt × M →ₒ Range).QueryCache))] := by
  unfold gpvStepProg
  simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, StateT.run_set,
    StateT.run_map, bind_pure_comp, map_pure, Functor.map_map, monadLift_self]

/-! ## Front-loading the adaptive salt draws into `signRunF`

The remaining content of `AdaptiveFactorizesSignRunF` against the concrete handlers above is the
pair of run-equalities together with the cache-growth bound on the recorded slices. These facts are
*not* structural: they assert that the adaptive real / programmed game runs
`simulateQ impl (adv.main pk)` (where each signing query draws a fresh salt at an
adversary-chosen point and queries the random oracle at it) factor through the *fixed* `qSign`-step
`signRunF` recursion with the concrete `gpvStepReal` / `gpvStepProg` handlers and a common recorded
cache sequence `c` with `card (c j) ≤ j + qHash`.

Establishing this is the deferred-sampling fold-level coupling: every fresh salt draw, currently
issued inside the signing oracle at an adversarially-chosen point in an adaptively-interleaved query
stream, is *commuted to the front* of a clean `qSign`-step draw sequence (the salts are fresh
uniform and independent of the adversary view until revealed; the interleaved hash queries are
answer-irrelevant w.r.t. the salt draws and so commute). This is the GPV instance of the worked
Fiat–Shamir factorization
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`: an induction on
`adv.main pk` via `OracleComp.inductionOn`, with the uniform / hash-read steps handled by the
generic `OracleComp.DeferredSampling.evalDist_step_commute_tape` answer-irrelevant commute and the
signing step handled by a bespoke per-body salt splice. -/

/-! ### The pinned GPV game runs

The front-tape coupling `gpv_tvDist_tape_runs_le_collisionBound` is pinned to the *actual* GPV game
runs of the adversary's main computation `adv.main pk`, not to free `SPMF` parameters or to a
hash-only run under a deterministic programming policy. Two named game-run distributions model the
two worlds of the sign-then-hash hop:

- `realGameRun` is the **real EUF-CMA game run**: `adv.main pk` simulated under the real ambient
  oracle forwarding (the lazy random oracle via the `runtime` bundle) and the real GPV signing
  oracle (`SignatureAlg.signingOracle`, which on each signing query draws a fresh salt, queries the
  random oracle, and trapdoor-samples a preimage). This is exactly the inner run of
  `SignatureAlg.unforgeableExpNoFresh` for the GPV scheme, with the forgery `(msg, σ)` extracted.

- `progGameRun` is the **randomized sign-then-hash game run**: `adv.main pk` simulated under the
  *programmed* random oracle and the *simulator* signing oracle of the collision reduction
  (the very handler stack of `reduction`). On each random-oracle miss the programmed oracle
  forward-samples `s ← domainSample pk` and records `psf.eval pk s`; on each signing query the
  simulator draws a fresh salt `r`, forward-samples `s`, programs `(r, msg) := psf.eval pk s`, and
  returns `(r, s)`. The randomness is genuine (it lives in `domainSample`), so this models the
  randomized sign-then-hash game rather than a deterministic point-mass programming policy.

The total-variation distance between these two runs is the sign-then-hash hop bounded by
`collisionBound`; the coupling factors both through the `signRunF` presentation so that
`factorized_advantage_le_collisionBound` delivers the bound. -/

open Classical in
/-- **The real GPV EUF-CMA game run** of `adv.main pk` at key pair `(pk, sk)`.

The adversary's main computation is simulated under the real ambient oracle forwarding (the lazy
random oracle supplied by the `runtime` bundle) together with the real GPV signing oracle
(`SignatureAlg.signingOracle`), and the resulting forgery `(msg, σ)` is extracted. This is exactly
the inner run of `SignatureAlg.unforgeableExpNoFresh` for the GPV scheme: it is the real-world side
of the sign-then-hash hop, the coupling's `realRun`. -/
noncomputable def realGameRun
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    SPMF (M × (Salt × Domain)) :=
  (runtime M Salt).evalDist do
    let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        (WriterT (QueryLog (M →ₒ (Salt × Domain)))
          (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
      (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
          (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
        (WriterT (QueryLog (M →ₒ (Salt × Domain)))
          (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
        (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).signingOracle pk sk
    let (out, _log) ← (simulateQ impl (adv.main pk)).run
    pure out

open Classical in
/-- **The randomized sign-then-hash game run** of `adv.main pk` at public key `pk`.

The adversary's main computation is simulated under the collision reduction's programmed
random-oracle / simulator-signing handler stack (the handler model of `reduction`): on a
random-oracle miss the oracle forward-samples `s ← domainSample pk` and records `psf.eval pk s`; on
a signing query the simulator draws a fresh salt `r`, forward-samples `s`, programs
`(r, msg) := psf.eval pk s`, and returns `(r, s)`. The forgery `(msg, σ)` is extracted. The
programming is *randomized* (the randomness lives in `domainSample`), so this models the randomized
sign-then-hash game; it is the coupling's `progRun`. -/
noncomputable def progGameRun
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    SPMF (M × (Salt × Domain)) :=
  let State := (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let s ← (domainSample pk : ProbComp Domain)
          let v := psf.eval pk s
          set ((st.1.cacheQuery t v, fun t' => if t' = t then some s else st.2 t') : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let s ← (domainSample pk : ProbComp Domain)
      let v := psf.eval pk s
      let st ← get
      set ((st.1.cacheQuery (r, msg) v,
        fun t' => if t' = (r, msg) then some s else st.2 t') : State)
      pure (r, s)
  let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT State ProbComp) := (unifImpl + roImpl) + signImpl
  𝒟[Prod.fst <$> (simulateQ impl (adv.main pk)).run (∅, fun _ => none)]

/-! ### Collapsing the runtime indirection of `realGameRun`

The real-side run-equality compares `realGameRun` — defined through the bundled `runtime` `SPMF`
semantics, which is *itself* a `simulateQ` (`withStateOracle`) over a `StateT` random-oracle layer
wrapping the WriterT signing-oracle `simulateQ` — against the single-`simulateQ` `signRunF`
presentation. Before that fold coupling is attempted with the generic handler-congruence /
`inductionOn` machinery, the *outer* runtime indirection of `realGameRun` is peeled back to an
explicit `simulateQ` form. The two lemmas below do exactly that peeling (and nothing more): they are
pure structural unfoldings of the `runtime` bundle, pinned to the concrete `realGameRun`, and do
**not** perform any distributional coupling. -/

/-- **`withStateOracle` `SPMF` semantics as an explicit `simulateQ` run (general).**

The bundled `withStateOracle hashImpl s` `SPMF` semantics of a surface computation `mx` is exactly
the observed `StateT.run'` of the `simulateQ` of the public-randomness lift summed with the stateful
`hashImpl`, started from `s`. This is a definitional unfolding of the bundle (`evalDist` is
`denote = observe ∘ interpret`, with `interpret = simulateQ'` and
`observe = liftM ∘ StateT.run' · s`) and carries no probabilistic content; it is the entry point for
reasoning about the runtime layer of
`realGameRun` by an explicit `simulateQ`. -/
theorem withStateOracle_evalDist_eq {ι : Type} {hashSpec : OracleSpec ι} {σ : Type}
    (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)
    {α : Type} (mx : OracleComp (unifSpec + hashSpec) α) :
    (SPMFSemantics.withStateOracle hashImpl s).evalDist mx
      = (liftM (StateT.run'
          (simulateQ
            ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) + hashImpl)
            mx) s) : SPMF α) := by
  unfold SPMFSemantics.evalDist SPMFSemantics.withStateOracle
  simp only [SemanticsVia.denote]

/-- **WriterT-log discard across a substituting oracle (general).**

Simulating `oa` under a WriterT-valued query implementation `so` and then projecting away the
written log (`Prod.fst <$> (·).run`) coincides with simulating `oa` under the *unlogged* base-spec
implementation `soNoLog`, provided the two agree per query after the same log discard
(`hso : ∀ t, Prod.fst <$> (so t).run = soNoLog t`).

Unlike `OracleComp.fst_map_writerT_run_simulateQ`, the target base spec `specBase` may differ from
the source spec `spec`: `soNoLog` is allowed to *substitute* each query by an arbitrary base-spec
computation (not merely re-emit it), so this applies to a genuine oracle replacement such as the GPV
signing oracle (which replaces an abstract signing query by its real `sign` computation over the
random-oracle spec). It is proved by induction on `oa`, with the append-accumulated WriterT log on
the binder collapsing under `Prod.fst`. The log carrier uses the append-based `WriterT` monad
(`[EmptyCollection ω] [Append ω] [LawfulAppend ω]`) so that it applies directly to the `QueryLog`
log of the GPV signing oracle, whose `WriterT` monad instance is the append-based one (there is
deliberately no `Monoid (QueryLog spec)` instance). -/
theorem fst_map_writerT_run_simulateQ_noLog
    {ι ιB : Type} {spec : OracleSpec ι} {specBase : OracleSpec ιB}
    {ω : Type} [EmptyCollection ω] [Append ω] [LawfulAppend ω] {α : Type}
    (so : QueryImpl spec (WriterT ω (OracleComp specBase)))
    (soNoLog : QueryImpl spec (OracleComp specBase))
    (hso : ∀ (t : spec.Domain),
      (Prod.fst <$> (so t).run : OracleComp specBase _) = soNoLog t)
    (oa : OracleComp spec α) :
    (Prod.fst <$> (simulateQ so oa).run : OracleComp specBase α) = simulateQ soNoLog oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [WriterT.run_pure]
  | query_bind t oa ih =>
    rw [simulateQ_bind, simulateQ_query, WriterT.run_bind, map_bind]
    have heq : ((OracleSpec.query t).cont <$> so (OracleSpec.query t).input) = so t := by
      simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]
    rw [heq]
    rw [show simulateQ soNoLog (liftM (OracleSpec.query t) >>= oa)
          = soNoLog t >>= fun u => simulateQ soNoLog (oa u) by
        rw [simulateQ_bind, simulateQ_query]
        simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]]
    refine (bind_congr fun x => ?_).trans (by rw [← bind_map_left, hso t])
    obtain ⟨a, w₁⟩ := x
    dsimp only []
    rw [← LawfulFunctor.comp_map]
    have : Prod.fst ∘ (fun x : α × ω ↦ (x.1, w₁ ++ x.2)) = Prod.fst :=
      funext fun ⟨_, _⟩ => rfl
    rw [this]
    exact ih a

/-- **The unlogged real GPV handler stack.**

The real-world handler used inside `realGameRun` is the WriterT-valued stack
`(HasQuery.toQueryImpl).liftTarget (WriterT …) + signingOracle pk sk`, which logs each signing
query. `realGameRunImplNoLog` is the same handler with the signing log discarded: the public/random
oracle queries are re-emitted unchanged into the underlying `OracleComp (unifSpec + (Salt × M →ₒ
Range))`, and each signing query is replaced by the real GPV `sign pk sk` computation (draw a fresh
salt, query the random oracle, trapdoor-sample). It targets `OracleComp (unifSpec + (Salt × M →ₒ
Range))` directly, so simulating `adv.main pk` under it produces the same forgery distribution as
the logged stack with its log discarded (`realGameRun_writerLog_discard`). -/
noncomputable def realGameRunImplNoLog (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (OracleComp (unifSpec + (Salt × M →ₒ Range))) :=
  (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
      (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
    (fun msg => (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
      psf hr M Salt).sign pk sk msg)

omit [Fintype Salt] in
/-- **Real-side WriterT-log discard (pinned).**

Discarding the signing log from the real GPV WriterT handler stack of `realGameRun` leaves exactly
the unlogged stack `realGameRunImplNoLog`: projecting the first component of the WriterT run of
`simulateQ ((HasQuery.toQueryImpl).liftTarget (WriterT …) + signingOracle pk sk) (adv.main pk)`
equals `simulateQ (realGameRunImplNoLog …) (adv.main pk)`.

It is *pinned* to the concrete real GPV handler stack and is a pure structural rewrite (the general
`fst_map_writerT_run_simulateQ_noLog` discharged by the per-query log-transparency of the two
summands: the lifted public/random-oracle handler re-emits its query, and
`signingOracle = withLogging sign` recovers `sign` after the log discard). No salt front-loading or
distributional coupling is
performed; this is the WriterT-boundary half of the real-side normalization toward the single-impl
`signRunF` shape. -/
theorem realGameRun_writerLog_discard (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (Prod.fst <$> (simulateQ
        (((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
            (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).signingOracle pk sk))
        (adv.main pk)).run
        : OracleComp (unifSpec + (Salt × M →ₒ Range)) (M × (Salt × Domain)))
      = simulateQ (realGameRunImplNoLog psf hr M Salt pk sk) (adv.main pk) := by
  refine fst_map_writerT_run_simulateQ_noLog _ _ (fun t => ?_) (adv.main pk)
  rcases t with t | msg
  · change (Prod.fst <$> ((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
        (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
        (WriterT (QueryLog (M →ₒ (Salt × Domain)))
          (OracleComp (unifSpec + (Salt × M →ₒ Range)))) t).run
        : OracleComp (unifSpec + (Salt × M →ₒ Range)) _)
      = realGameRunImplNoLog psf hr M Salt pk sk (Sum.inl t)
    simp only [QueryImpl.liftTarget_apply, WriterT.run_liftM]
    rfl
  · change (Prod.fst <$> ((GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
        psf hr M Salt).signingOracle pk sk msg).run
        : OracleComp (unifSpec + (Salt × M →ₒ Range)) _)
      = (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).sign pk sk msg
    simp only [SignatureAlg.signingOracle, QueryImpl.withLogging_apply, bind_pure_comp,
      WriterT.run_bind, WriterT.run_liftM, bind_map_left]
    simp only [WriterT.run_map, WriterT.run_tell, map_pure]
    rw [← Functor.map_map]
    simp

open Classical in
omit [Fintype Salt] in
/-- **Real-side normalization (pinned): `realGameRun` as an explicit two-layer
`simulateQ` run.**

This peels the bundled `runtime` indirection off `realGameRun`, exposing the *explicit* nested
`simulateQ` form: the inner WriterT signing-oracle `simulateQ` over `adv.main pk` (its `.run`
discarding the signing log to the `Prod.fst` projection), evaluated under the outer
public-randomness-lift `+ randomOracle` `StateT QueryCache ProbComp` `simulateQ`, observed by
`StateT.run'` from the empty cache.

It is *pinned* to the concrete `realGameRun` (it is an equation about that exact distribution, with
the concrete WriterT handler stack `liftTarget HasQuery.toQueryImpl + signingOracle pk sk` and the
concrete outer lazy random oracle), and it is a pure structural rewrite — the trailing `pure out`
of the `realGameRun` do-block is commuted out by `withStateOracle_evalDist_bind_pure`, and the
runtime layer is unfolded by `withStateOracle_evalDist_eq`. No salt front-loading and no
distributional coupling is performed; this is the runtime-indirection removal that the deep fold
coupling builds on. -/
theorem realGameRun_eq_simulateQ_run
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    realGameRun psf hr M Salt adv pk sk =
      Prod.fst <$> ((SPMFSemantics.withStateOracle
        (randomOracle : QueryImpl (Salt × M →ₒ Range)
          (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalDist
        ((simulateQ
            (((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
              (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                psf hr M Salt).signingOracle pk sk))
            (adv.main pk)).run)) := by
  unfold realGameRun
  rw [show (do
        let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
          (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
              (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
            (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
              psf hr M Salt).signingOracle pk sk
        let (out, _log) ← (simulateQ impl (adv.main pk)).run
        pure out) = ((simulateQ
            (((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
              (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                psf hr M Salt).signingOracle pk sk))
            (adv.main pk)).run >>= fun p => pure p.1) from rfl]
  rw [GPVHashAndSign.runtime]
  change (SPMFSemantics.withStateOracle _ ∅).evalDist _ = _
  rw [SPMFSemantics.withStateOracle_evalDist_bind_pure]

open Classical in
omit [Fintype Salt] in
/-- **Real-side normalization (pinned, single-impl): `realGameRun` as one bundled
`simulateQ` over the unlogged real handler stack.**

This is the assembled real-side normalization: `realGameRun` equals the bundled `withStateOracle`
random-oracle `SPMF` semantics of `simulateQ (realGameRunImplNoLog …) (adv.main pk)` — a *single*
`OracleComp (unifSpec + (Salt × M →ₒ Range))`-valued `simulateQ` over the unlogged real GPV handler
stack, with no remaining WriterT layer. It chains `realGameRun_eq_simulateQ_run` (peeling the
`runtime` indirection and commuting the trailing `pure out` to `Prod.fst <$>`),
`SPMFSemantics.withStateOracle_evalDist_map` (pushing that `Prod.fst <$>` *inside* the outer
bundle, since `<$>` does not thread the random-oracle state), and `realGameRun_writerLog_discard`
(collapsing the inner WriterT signing-log run to `realGameRunImplNoLog`).

It is *pinned* to the concrete `realGameRun` and is purely structural (no salt front-loading, no
distributional coupling). This is the canonical single-`simulateQ` shape that the eventual fold
coupling consumes: `realGameRun`'s adversary computation is now interpreted by one ambient handler
`realGameRunImplNoLog` over `OracleComp (unifSpec + (Salt × M →ₒ Range))`, then observed by the
random-oracle `withStateOracle` bundle — the same surface shape carried by `progGameRun`'s single
`StateT`-state `simulateQ`. -/
theorem realGameRun_eq_withStateOracle_implNoLog
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    realGameRun psf hr M Salt adv pk sk =
      (SPMFSemantics.withStateOracle
        (randomOracle : QueryImpl (Salt × M →ₒ Range)
          (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalDist
        (simulateQ (realGameRunImplNoLog psf hr M Salt pk sk) (adv.main pk)) := by
  rw [realGameRun_eq_simulateQ_run, ← SPMFSemantics.withStateOracle_evalDist_map,
    realGameRun_writerLog_discard]

/-! ### Dropping the preimage-record component of `progGameRun`

`progGameRun` simulates `adv.main pk` under a handler stack whose state is the product
`QueryCache × ((Salt × M) → Option Domain)`. The second component is the *preimage record*: it
records, for each programmed random-oracle point, the domain element forward-sampled to produce the
answer. That record is bookkeeping for the collision reduction's extraction only — it is written by
every programming step (and read solely to update *itself*), but it never influences the
random-oracle cache, the output, or any other branch. Hence the forgery distribution `progGameRun`
(the `Prod.fst` of the run) is unchanged by dropping the record component, leaving a single
`simulateQ` over the bare
`StateT QueryCache ProbComp` random-oracle surface — the *same* state shape carried by
`realGameRunImplNoLog` under the runtime `withStateOracle` bundle. The lemma below performs exactly
that drop (no distributional coupling). -/

/-- **The record-free `progGameRun` handler stack.**

The same programmed random-oracle / simulator-signing handler stack as `progGameRun`, but with the
preimage-record component removed: its state is just the random-oracle `QueryCache`. The
random-oracle handler programs a miss with `psf.eval pk (domainSample pk)`; the signing handler
draws a fresh salt, forward-samples, programs the cache point, and returns `(r, s)`. This carries
the same
`StateT QueryCache ProbComp` random-oracle surface as `realGameRunImplNoLog` (observed through the
runtime `withStateOracle` bundle), the shared shape required before the fold coupling. -/
noncomputable def progGameRunImplNoRec (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
  let roImpl : QueryImpl (Salt × M →ₒ Range)
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
    fun t => do
      let st ← get
      match st t with
      | some v => pure v
      | none => do
          let s ← (domainSample pk : ProbComp Domain)
          let v := psf.eval pk s
          set (st.cacheQuery t v)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let s ← (domainSample pk : ProbComp Domain)
      let v := psf.eval pk s
      let st ← get
      set (st.cacheQuery (r, msg) v)
      pure (r, s)
  (unifImpl + roImpl) + signImpl

open Classical in
omit [Fintype Salt] in
/-- **Prog-side normalization (pinned): `progGameRun` with the preimage record dropped.**

`progGameRun … adv domainSample pk` equals the random-oracle `SPMF` semantics of the *single*
`simulateQ (progGameRunImplNoRec …) (adv.main pk)` over the bare `StateT QueryCache ProbComp` state,
observed by `StateT.run'` from the empty cache. The preimage-record component of `progGameRun`'s
state is genuinely passive: it is written by the programming steps but never read by the cache, the
output, or the control flow, so projecting it away (`proj = Prod.fst`) commutes with every oracle
step and hence with the whole simulation (`map_run_simulateQ_eq_of_query_map_eq`).

It is *pinned* to the concrete `progGameRun` and is a pure structural state-projection (no salt
front-loading, no distributional coupling). Together with `realGameRun_eq_withStateOracle_implNoLog`
this puts **both** game runs on the same `StateT QueryCache ProbComp` random-oracle surface — the
prerequisite for the `OracleComp.inductionOn` fold coupling. -/
theorem progGameRun_eq_run'_implNoRec
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    progGameRun psf hr M Salt adv domainSample pk =
      𝒟[(simulateQ (progGameRunImplNoRec psf M Salt domainSample pk)
          (adv.main pk)).run' (∅ : (Salt × M →ₒ Range).QueryCache)] := by
  unfold progGameRun
  simp only [evalDist]
  refine congrArg _ ?_
  -- LHS is `Prod.fst <$> run = run'`; the record component (initially `fun _ => none`) is the
  -- passive auxiliary, so the state projection `proj = Prod.fst` commutes with every step.
  rw [show ((∅ : (Salt × M →ₒ Range).QueryCache)) = Prod.fst
      (((∅ : (Salt × M →ₒ Range).QueryCache), (fun _ => none : (Salt × M) → Option Domain))) from
        rfl]
  rw [← StateT.run']
  refine run'_simulateQ_eq_of_query_map_eq _
    (progGameRunImplNoRec psf M Salt domainSample pk) Prod.fst ?_ (adv.main pk)
    (∅, fun _ => none)
  -- For each oracle (uniform / random-oracle / signing) the cache update depends only on the
  -- cache component, so projecting away the preimage record commutes with the step.
  rintro ((t | t) | t) ⟨st, rec⟩ <;>
    simp only [HAdd.hAdd, QueryImpl.add, progGameRunImplNoRec]
  · -- uniform-sampling query: state untouched by either handler
    simp [StateT.run_monadLift, Prod.map]
  · -- random-oracle query: the cache hit/miss is determined by the cache component `st t`
    rcases h : st t with _ | v <;>
      simp [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, Prod.map, h]
  · -- signing query: cache update depends only on the cache component
    simp [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_monadLift, Prod.map]

/-- **The composed single-impl real GPV handler stack.**

The two-layer real-side simulation of `realGameRun` — `simulateQ realGameRunImplNoLog (adv.main pk)`
producing an `OracleComp (unifSpec + (Salt × M →ₒ Range))`, then observed by the runtime's
public-randomness-lift `+ randomOracle` `StateT QueryCache ProbComp` simulation — fused into a
*single* `StateT QueryCache ProbComp`-valued handler via `QueryImpl.compose` (`∘ₛ`). This carries
the same bare `StateT QueryCache ProbComp` random-oracle surface as `progGameRunImplNoRec`, the
shared shape the fold coupling consumes. -/
noncomputable def gpvRealImpl (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
  (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) +
      (randomOracle : QueryImpl (Salt × M →ₒ Range)
        (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))) ∘ₛ
    realGameRunImplNoLog psf hr M Salt pk sk)

open Classical in
omit [Fintype Salt] in
/-- **Real-side single-impl normalization (pinned): `realGameRun` as one bundled `simulateQ`
over the composed real handler `gpvRealImpl`.**

This collapses the two-layer real-side simulation of `realGameRun` into a single `simulateQ` over
the composed handler `gpvRealImpl` (`= outerLift ∘ₛ realGameRunImplNoLog`), observed by
`StateT.run'` from the empty cache:
`realGameRun … = 𝒟[(simulateQ (gpvRealImpl …) (adv.main pk)).run' ∅]`. It
chains `realGameRun_eq_withStateOracle_implNoLog` (the peeling of the runtime indirection to
a single `simulateQ realGameRunImplNoLog` observed through `withStateOracle`),
`withStateOracle_evalDist_eq` (unfolding the `withStateOracle` bundle to an explicit
`StateT.run'`-of-`simulateQ` of the public-randomness lift `+ randomOracle`), and
`QueryImpl.simulateQ_compose` (fusing the two `simulateQ` layers into the single composed handler).

It is *pinned* to the concrete `realGameRun` and is a pure structural normalization — no salt
front-loading, no distributional coupling. Together with `progGameRun_eq_run'_implNoRec` this puts
**both** game runs in the identical `𝒟[(simulateQ · (adv.main pk)).run' ∅]` shape over the *same*
`StateT QueryCache ProbComp` random-oracle surface, the prerequisite for attempting the
`OracleComp.inductionOn` fold coupling on a common vehicle. -/
theorem realGameRun_eq_run'_implReal
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) :
    realGameRun psf hr M Salt adv pk sk =
      𝒟[(simulateQ (gpvRealImpl psf hr M Salt pk sk)
          (adv.main pk)).run' (∅ : (Salt × M →ₒ Range).QueryCache)] := by
  rw [realGameRun_eq_withStateOracle_implNoLog, withStateOracle_evalDist_eq]
  rw [← QueryImpl.simulateQ_compose]
  rfl

/-! ### GPV tape-consuming impls

The fold coupling `gpv_tvDist_tape_runs_le_collisionBound` follows the worked Fiat–Shamir instance
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`: an
`OracleComp.inductionOn`
over `adv.main pk` that front-loads every signing query's fresh salt draw into a single front draw
block `OracleComp.drawList ($ᵗ Salt) qSign`, leaving a *tape-consuming* run whose signing steps read
their salt off the pre-drawn tape rather than drawing it inline.

This section builds the GPV tape-consuming handlers — the analogues of Fiat–Shamir's
`tapeDrawReadImpl` — and their per-query `.run` unfolding lemmas (the analogues of
`tapeDrawReadImpl_run_unif` / `_read` / `_sign`). Each handler carries the random-oracle
`QueryCache` *plus a salt tape* `List Salt` in its state: a signing query consumes the head salt of
the tape (running the rest of the inline signing body on it) instead of drawing `r ← $ᵗ Salt`, while
uniform and random-oracle-read queries leave the tape untouched. These are concrete definitions and
their structural per-query unfoldings; the full `inductionOn` factorization (relating
`simulateQ gpvRealImpl` to the front-tape `drawList ($ᵗ Salt) qSign >>= simulateQ gpvRealImplTape`)
and the `drawList`↔`signRunF` bridge are carried out in the front-tape factorization below. -/

/-- **The real GPV tape-consuming handler.**

The salt-tape analogue of `gpvRealImpl`: its state is the random-oracle `QueryCache` paired with a
*salt tape* `List Salt`. A signing query consumes the head salt `r` of the tape (instead of drawing
`r ← $ᵗ Salt` inline), queries the random oracle at `(r, msg)`, trapdoor-samples a preimage, and
returns `(r, s)` while advancing the tape by one; uniform and random-oracle-read queries behave
exactly as the real handler and leave the tape untouched. The tape is over-provisioned (length
`qSign`, one salt per signing query); a missing head (empty tape) defaults to the inline draw so the
handler is total. This is the GPV analogue of Fiat–Shamir's `tapeDrawReadImpl`; its per-query
unfoldings are recorded by `gpvRealImplTape_run_unif` / `_read` / `_sign` below. -/
noncomputable def gpvRealImplTape (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × List Salt) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, s.2))) <$>
        (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1
  | .inr msg => StateT.mk fun s =>
      match s.2 with
      | [] =>
          (fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache =>
              (rsc.1, (rsc.2, ([] : List Salt)))) <$>
            (do
              let r ← ($ᵗ Salt : ProbComp Salt)
              let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
              let sgn ← psf.trapdoorSample pk sk p.1
              pure ((r, sgn), p.2))
      | r :: tl =>
          (fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache => (rsc.1, (rsc.2, tl))) <$>
            (do
              let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
              let sgn ← psf.trapdoorSample pk sk p.1
              pure ((r, sgn), p.2))

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTape` on a uniform query.** The tape is untouched. -/
lemma gpvRealImplTape_run_unif (pk : PK) (sk : SK) (n : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _) := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTape` on a random-oracle read query.** The tape is
untouched; the cache component runs the lazy `randomOracle` step. -/
lemma gpvRealImplTape_run_read (pk : PK) (sk : SK) (mc : Salt × M)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run s =
      (fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, s.2))) <$>
        (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTape` on a signing query with a non-empty tape.** The head
salt `r` is consumed off the tape (the tape advances to its tail `tl`), the random oracle is queried
at `(r, msg)`, a trapdoor preimage is drawn, and `(r, s)` is returned. This is the GPV analogue of
`tapeDrawReadImpl_run_sign`: the inline salt draw `r ← $ᵗ Salt` is *replaced* by consuming the
pre-drawn tape head. -/
lemma gpvRealImplTape_run_sign_cons (pk : PK) (sk : SK) (msg : M) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImplTape psf M Salt pk sk (.inr msg)).run (cache, r :: tl) =
      (fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache => (rsc.1, (rsc.2, tl))) <$>
        (do
          let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
          let sgn ← psf.trapdoorSample pk sk p.1
          pure ((r, sgn), p.2)) := rfl

/-- **The programmed (simulator) GPV tape-consuming handler.**

The salt-tape analogue of `progGameRunImplNoRec`: its state is the random-oracle `QueryCache` paired
with a salt tape `List Salt`. A signing query consumes the head salt `r` of the tape (instead of
drawing `r ← $ᵗ Salt` inline), forward-samples a short preimage `s ← domainSample pk`, programs the
cache point `(r, msg) ↦ psf.eval pk s`, and returns `(r, s)` while advancing the tape; the
random-oracle handler programs a miss with `psf.eval pk (domainSample pk)` and the uniform handler
is the bare sample, both leaving the tape untouched. This is the programmed dual of
`gpvRealImplTape`; its per-query unfoldings are recorded by `progGameRunImplTape_run_unif` /
`_read` / `_sign` below. -/
noncomputable def progGameRunImplTape (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × List Salt) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr mc) => StateT.mk fun s =>
      match s.1 mc with
      | some v => pure (v, s)
      | none =>
          (fun sd : Domain => (psf.eval pk sd, (s.1.cacheQuery mc (psf.eval pk sd), s.2))) <$>
            (domainSample pk : ProbComp Domain)
  | .inr msg => StateT.mk fun s =>
      match s.2 with
      | [] =>
          (do
            let r ← ($ᵗ Salt : ProbComp Salt)
            let sd ← (domainSample pk : ProbComp Domain)
            pure ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), ([] : List Salt))))
      | r :: tl =>
          (fun sd : Domain => ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), tl))) <$>
            (domainSample pk : ProbComp Domain)

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTape` on a uniform query.** The tape is untouched. -/
lemma progGameRunImplTape_run_unif (domainSample : PK → ProbComp Domain) (pk : PK)
    (n : unifSpec.Domain) (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _) := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTape` on a random-oracle read query.** The tape is
untouched; on a cache hit the recorded value is returned, on a miss the answer is programmed to
`psf.eval pk (domainSample pk)`. -/
lemma progGameRunImplTape_run_read (domainSample : PK → ProbComp Domain) (pk : PK) (mc : Salt × M)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run s =
      (match s.1 mc with
        | some v => pure (v, s)
        | none =>
            (fun sd : Domain => (psf.eval pk sd, (s.1.cacheQuery mc (psf.eval pk sd), s.2))) <$>
              (domainSample pk : ProbComp Domain)) := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTape` on a signing query with a non-empty tape.** The
head salt `r` is consumed off the tape (the tape advances to its tail `tl`), a short preimage is
forward-sampled, the cache point `(r, msg) ↦ psf.eval pk s` is programmed, and `(r, s)` is returned.
This is the programmed analogue of `gpvRealImplTape_run_sign_cons`: the inline salt draw is replaced
by consuming the pre-drawn tape head. -/
lemma progGameRunImplTape_run_sign_cons (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (r : Salt) (tl : List Salt) (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run (cache, r :: tl) =
      (fun sd : Domain => ((r, sd), (cache.cacheQuery (r, msg) (psf.eval pk sd), tl))) <$>
        (domainSample pk : ProbComp Domain) := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **Real tape signing-step cache bridge.** The cache component of one `gpvRealImplTape` signing
step on a consed tape `r :: tl`, at a *missing* cache key `(r, msgs n) = none`, is distributed
exactly as the concrete `signRunF` real step `gpvStepReal` at the consumed head salt `r`.

This is the GPV analogue of Fiat–Shamir's per-body splice (the signing-step case of the fold
factorization): it relates the tape-consuming signing step to the `signRunF` handler underlying
`gpv_tvDist_tape_runs_le_collisionBound`. It is *pinned* to the concrete
`gpvRealImplTape` and
`gpvStepReal`, and reduces (via `gpvRealImplTape_run_sign_cons`) to the inline splice
`evalDist_gpvSignBody_run_eq_gpvStepReal`: with the head salt `r` already supplied (front-loaded out
of the tape), the tape signing step is exactly one real signing body run through the lazy random
oracle, whose recorded cache transition is `gpvStepReal n cache r`. The only side condition is the
fresh-salt cache miss `hmiss`. -/
lemma evalDist_gpvRealImplTape_sign_cache_eq_gpvStepReal (pk : PK) (sk : SK) (msgs : ℕ → M) (n : ℕ)
    (r : Salt) (tl : List Salt) (cache : (Salt × M →ₒ Range).QueryCache)
    (hmiss : cache (r, msgs n) = none) :
    𝒟[(fun p : (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.2.1) <$>
        (gpvRealImplTape psf M Salt pk sk (.inr (msgs n))).run (cache, r :: tl)]
      = 𝒟[gpvStepReal psf M Salt pk sk msgs n cache r] := by
  rw [gpvRealImplTape_run_sign_cons]
  simp only [Functor.map_map]
  rw [← evalDist_gpvSignBody_run_eq_gpvStepReal psf M Salt pk sk msgs n cache r hmiss]
  simp [map_bind]

open Classical in
omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Programmed tape signing-step cache bridge.** The cache component of one
`progGameRunImplTape` signing step on a consed tape `r :: tl` is distributed exactly as the concrete
`signRunF` programmed step `gpvStepProg` at the consumed head salt `r`.

This is the programmed dual of `evalDist_gpvRealImplTape_sign_cache_eq_gpvStepReal`, and the
signing-step case of the *programmed* run-equality the coupling factors through. It is *pinned* to
the concrete `progGameRunImplTape` and `gpvStepProg`: both forward-sample `s ← domainSample pk` and
record the cache transition `cache ↦ cache.cacheQuery (r, msgs n) (psf.eval pk s)` at the consumed
head salt `r`, so projecting the random-oracle cache component yields exactly `gpvStepProg`. No
side condition is required (the programmed step caches unconditionally). -/
lemma evalDist_progGameRunImplTape_sign_cache_eq_gpvStepProg (domainSample : PK → ProbComp Domain)
    (pk : PK) (msgs : ℕ → M) (n : ℕ) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    𝒟[(fun p : (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.2.1) <$>
        (progGameRunImplTape psf M Salt domainSample pk (.inr (msgs n))).run (cache, r :: tl)]
      = 𝒟[gpvStepProg psf M Salt pk domainSample msgs n cache r] := by
  rw [progGameRunImplTape_run_sign_cons]
  unfold gpvStepProg
  simp [map_eq_bind_pure_comp, Function.comp]

omit [Fintype Salt] [DecidableEq Range] in
/-- **Off-bad joint agreement of the two tape signing steps on a fresh head salt (the `hreg`
substitution bridge, signing case).** On a non-empty tape `r :: tl` whose head salt `r` is *not yet
keyed* in the cache — so the random-oracle read at `(r, msg)` is a miss — the full signing-step
output distributions of `gpvRealImplTape` and `progGameRunImplTape` *coincide*: the returned
signature `(r, sgn)`, the updated cache, and the advanced tape `tl` are jointly distributed the same
on both sides.

The real side draws a fresh uniform target `c ← $ᵗ Range`, a trapdoor preimage `sgn ←
trapdoorSample pk sk c`, records `(r, msg) ↦ c`, and returns `((r, sgn), cache', tl)`; the
programmed side forward-samples `sd ← domainSample pk`, records `(r, msg) ↦ psf.eval pk sd`, and
returns `((r, sd), cache'', tl)`. Both apply the *same* deterministic post-processing
`fun (c, s) => ((r, s), cache.cacheQuery (r, msg) c, tl)` to a `(target, preimage)` pair drawn from
two distributions that coincide by PSF regularity `hreg`. This is the signing-query case of the
per-step no-bad-path agreement underlying `gpv_tvDist_tape_runs_le_collisionBound`, the full-output
generalization of the cache-marginal `gpvStep_agree`. -/
theorem evalDist_gpvImplTape_run_sign_miss_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (msg : M) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) (hmiss : cache (r, msg) = none)
    (hreg : 𝒟[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒟[(gpvRealImplTape psf M Salt pk sk (.inr msg)).run (cache, r :: tl)]
      = 𝒟[(progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run (cache, r :: tl)] := by
  classical
  rw [gpvRealImplTape_run_sign_cons, progGameRunImplTape_run_sign_cons]
  -- The shared post-processing of a `(target, preimage)` pair.
  set g : Range × Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt) :=
    fun cs => ((r, cs.2), (cache.cacheQuery (r, msg) cs.1, tl)) with hg
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        = (fun u => (u, cache.cacheQuery (r, msg) u)) <$> ($ᵗ Range : ProbComp Range)
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  -- Both sides reduce to `g <$> (·)` applied to the two `hreg`-equal `(target, preimage)` draws.
  have hLHS :
      𝒟[((fun rsc : (Salt × Domain) × (Salt × M →ₒ Range).QueryCache => (rsc.1, (rsc.2, tl))) <$>
          (do
            let p ← (fun u => (u, cache.cacheQuery (r, msg) u)) <$> ($ᵗ Range : ProbComp Range)
            let sgn ← psf.trapdoorSample pk sk p.1
            pure ((r, sgn), p.2)))]
        = 𝒟[g <$> (do let c ← ($ᵗ Range); let sgn ← psf.trapdoorSample pk sk c; pure (c, sgn)
              : ProbComp (Range × Domain))] := by
    simp only [hg, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  have hRHS :
      𝒟[((fun sd : Domain => ((r, sd), (cache.cacheQuery (r, msg) (psf.eval pk sd), tl))) <$>
          (domainSample pk : ProbComp Domain))]
        = 𝒟[g <$> (do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
              : ProbComp (Range × Domain))] := by
    simp only [hg, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  exact evalDist_map_eq_of_evalDist_eq hreg.symm g

/-! ### Flag-instrumented tape handlers (the identical-until-bad collision flag)

The per-tape identical-until-bad coupling `gpv_tvDist_tape_runs_le_collisionBound` is
established, in the Fiat–Shamir template, by instrumenting the two tape handlers with a
collision *flag*: a `Bool` threaded through the state, set the first time a consumed signing tape
head salt `r` is already a key of the running random-oracle cache. Off the flag (no salt has yet
collided) the two handlers agree in distribution by the `hreg` first marginal; once the flag fires
it stays set (bad-monotone). The framework lemma `tvDist_simulateQ_run_le_probEvent_output_bad`
then bounds the per-tape TV by the run-level flag probability, which the cardinality telescope
(`saltSeq` / `tapeCheck`) bounds by `collisionBound`.

`saltKeyed cache r` is the per-step bad predicate: the head salt `r` is already a key of the cache
(some `(r, m)` is recorded). It is the collision event the flag accumulates. -/

open Classical in
/-- **Salt-already-keyed predicate.** `saltKeyed cache r` holds when the salt `r` already appears as
the first component of some recorded random-oracle key `(r, m)` in `cache`. It is the per-signing-
step collision event: a consumed signing tape head salt landing on a key the running cache already
holds. The flag-instrumented tape handlers set their collision flag exactly when this fires on the
consumed head salt. -/
noncomputable def saltKeyed (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) : Bool :=
  decide (∃ m : M, (cache (r, m)).isSome)

open Classical in
/-- **Flag-instrumented real tape handler.** `gpvRealImplTape` threaded with a collision flag: the
state is `((QueryCache × List Salt) × Bool)`. Uniform and random-oracle queries leave the flag
untouched; a signing query, before consuming its head salt `r`, sets the flag if `r` is already a
key of the cache (`saltKeyed`) on a non-empty tape, or unconditionally when the tape is *empty*
(no head salt to consume), monotonically OR-ing into the prior flag, then runs the underlying
`gpvRealImplTape` signing step. Its `run'`-projection (dropping the flag) is the original
`gpvRealImplTape`.

The empty-tape signing case fires the flag because there the underlying handler falls back to an
*inline* fresh salt draw that the tape-collision flag does not track, so the real and programmed
runs may diverge off-flag there; firing the flag makes the empty-tape signing state lie *inside*
the bad set, which is what makes the off-bad per-query agreement (`h_agree_good`) universal over all
states. In the actual `qSign`-salt run this branch is unreachable (the query bound permits at most
`qSign` signing queries and the tape holds `qSign` salts), so it contributes no probability mass. -/
noncomputable def gpvRealImplTapeFlag (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$> (gpvRealImplTape psf M Salt pk sk (.inl q)).run s.1
    | .inr msg =>
        let flag' : Bool := s.2 || (match s.1.2 with | r :: _ => saltKeyed M Salt s.1.1 r
                                                      | [] => true)
        (fun p => (p.1, (p.2, flag'))) <$> (gpvRealImplTape psf M Salt pk sk (.inr msg)).run s.1

open Classical in
/-- **Flag-instrumented programmed tape handler.** The programmed dual of `gpvRealImplTapeFlag`:
`progGameRunImplTape` threaded with the same collision flag (set on a signing step when the consumed
head salt `r` is already a key of the cache). Its `run'`-projection is the original
`progGameRunImplTape`. -/
noncomputable def progGameRunImplTapeFlag (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$>
          (progGameRunImplTape psf M Salt domainSample pk (.inl q)).run s.1
    | .inr msg =>
        let flag' : Bool := s.2 || (match s.1.2 with | r :: _ => saltKeyed M Salt s.1.1 r
                                                      | [] => true)
        (fun p => (p.1, (p.2, flag'))) <$>
          (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run s.1

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTapeFlag` on a non-signing query.** The flag is untouched;
the underlying `gpvRealImplTape` runs on the `(cache, tape)` component. -/
lemma gpvRealImplTapeFlag_run_inl (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    (gpvRealImplTapeFlag psf M Salt pk sk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$> (gpvRealImplTape psf M Salt pk sk (.inl q)).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTapeFlag` on a non-signing query.** -/
lemma progGameRunImplTapeFlag_run_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    (progGameRunImplTapeFlag psf M Salt domainSample pk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$>
        (progGameRunImplTape psf M Salt domainSample pk (.inl q)).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **One-step unfolding of `gpvRealImplTapeFlag` on a signing query.** The flag is OR-ed with the
collision predicate on the head salt (`saltKeyed` if the tape is non-empty, `false` otherwise), then
the underlying `gpvRealImplTape` signing step runs on the `(cache, tape)` component. -/
lemma gpvRealImplTapeFlag_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    (gpvRealImplTapeFlag psf M Salt pk sk (.inr msg)).run s =
      (fun p => (p.1, (p.2, s.2 || (match s.1.2 with
                                    | r :: _ => saltKeyed M Salt s.1.1 r
                                    | [] => true)))) <$>
        (gpvRealImplTape psf M Salt pk sk (.inr msg)).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **One-step unfolding of `progGameRunImplTapeFlag` on a signing query.** The programmed dual of
`gpvRealImplTapeFlag_run_inr`. -/
lemma progGameRunImplTapeFlag_run_inr (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    (progGameRunImplTapeFlag psf M Salt domainSample pk (.inr msg)).run s =
      (fun p => (p.1, (p.2, s.2 || (match s.1.2 with
                                    | r :: _ => saltKeyed M Salt s.1.1 r
                                    | [] => true)))) <$>
        (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run s.1 := rfl

omit [Fintype Salt] [DecidableEq Range] in
/-- **Per-query flag-projection of the real flag handler.** Dropping the flag component
(`Prod.map id Prod.fst`) from one `gpvRealImplTapeFlag` query step recovers the corresponding
`gpvRealImplTape` step on the flagless `(cache, tape)` state. The flag is a passive auxiliary: it is
written by the signing step but never affects the output, the cache, or the tape, so projecting it
away yields the original handler. This is the per-query hypothesis of the state-projection transport
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma gpvRealImplTapeFlag_proj_fst (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool →
        (Salt × M →ₒ Range).QueryCache × List Salt) <$>
        (gpvRealImplTapeFlag psf M Salt pk sk t).run s =
      (gpvRealImplTape psf M Salt pk sk t).run s.1 := by
  cases t with
  | inl q => rw [gpvRealImplTapeFlag_run_inl]; simp [Functor.map_map, Prod.map]
  | inr msg =>
      change Prod.map id Prod.fst <$> ((fun p => (p.1, (p.2,
          s.2 || (match s.1.2 with | r :: _ => saltKeyed M Salt s.1.1 r | [] => true)))) <$>
        (gpvRealImplTape psf M Salt pk sk (.inr msg)).run s.1) = _
      simp [Functor.map_map, Prod.map]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Per-query flag-projection of the programmed flag handler.** The programmed dual of
`gpvRealImplTapeFlag_proj_fst`: dropping the flag recovers `progGameRunImplTape`. -/
lemma progGameRunImplTapeFlag_proj_fst (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool →
        (Salt × M →ₒ Range).QueryCache × List Salt) <$>
        (progGameRunImplTapeFlag psf M Salt domainSample pk t).run s =
      (progGameRunImplTape psf M Salt domainSample pk t).run s.1 := by
  cases t with
  | inl q => rw [progGameRunImplTapeFlag_run_inl]; simp [Functor.map_map, Prod.map]
  | inr msg =>
      change Prod.map id Prod.fst <$> ((fun p => (p.1, (p.2,
          s.2 || (match s.1.2 with | r :: _ => saltKeyed M Salt s.1.1 r | [] => true)))) <$>
        (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run s.1) = _
      simp [Functor.map_map, Prod.map]

omit [Fintype Salt] [DecidableEq Range] in
/-- **Run-level flag-projection of the real flag handler.** Dropping the flag from the full
simulated run of `gpvRealImplTapeFlag` over `adv.main pk` recovers the flagless run of
`gpvRealImplTape`. This
transports the per-query projection `gpvRealImplTapeFlag_proj_fst` through the whole adversary via
`map_run_simulateQ_eq_of_query_map_eq`, witnessing that the collision flag is a passive instrument:
its addition does not change the output-and-`(cache, tape)` distribution. -/
lemma map_run_gpvRealImplTapeFlag_eq (pk : PK) (sk : SK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (M × (Salt × Domain)))
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool →
        (Salt × M →ₒ Range).QueryCache × List Salt) <$>
        (simulateQ (gpvRealImplTapeFlag psf M Salt pk sk) oa).run s =
      (simulateQ (gpvRealImplTape psf M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (gpvRealImplTapeFlag_proj_fst psf M Salt pk sk) oa s

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Run-level flag-projection of the programmed flag handler.** The programmed dual of
`map_run_gpvRealImplTapeFlag_eq`. -/
lemma map_run_progGameRunImplTapeFlag_eq (domainSample : PK → ProbComp Domain) (pk : PK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (M × (Salt × Domain)))
    (s : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool →
        (Salt × M →ₒ Range).QueryCache × List Salt) <$>
        (simulateQ (progGameRunImplTapeFlag psf M Salt domainSample pk) oa).run s =
      (simulateQ (progGameRunImplTape psf M Salt domainSample pk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (progGameRunImplTapeFlag_proj_fst psf M Salt domainSample pk) oa s

omit [Fintype Salt] [DecidableEq Range] in
/-- **Bad-monotonicity of the real flag handler.** Once the collision flag is set on the input state
(`p.2 = true`), every output of one `gpvRealImplTapeFlag` query step also carries the flag set: the
non-signing branch preserves `s.2`, and the signing branch only OR-s a new collision indicator into
it. This is the `h_mono` hypothesis the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` consumes: the bad event is absorbing. -/
lemma gpvRealImplTapeFlag_bad_mono (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((gpvRealImplTapeFlag psf M Salt pk sk t).run p), z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [gpvRealImplTapeFlag_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      have : z.2.2 = (p.2 || (match p.1.2 with
          | r :: _ => saltKeyed M Salt p.1.1 r | [] => true)) := by
        change z ∈ support ((fun w => (w.1, (w.2,
            p.2 || (match p.1.2 with | r :: _ => saltKeyed M Salt p.1.1 r | [] => true)))) <$>
          (gpvRealImplTape psf M Salt pk sk (.inr msg)).run p.1) at hz
        simp only [support_map, Set.mem_image] at hz
        obtain ⟨w, _, hw⟩ := hz
        simp [← hw]
      simp [this, hp]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Bad-monotonicity of the programmed flag handler.** The programmed dual of
`gpvRealImplTapeFlag_bad_mono`. -/
lemma progGameRunImplTapeFlag_bad_mono (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : ((Salt × M →ₒ Range).QueryCache × List Salt) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((progGameRunImplTapeFlag psf M Salt domainSample pk t).run p), z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [progGameRunImplTapeFlag_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      have : z.2.2 = (p.2 || (match p.1.2 with
          | r :: _ => saltKeyed M Salt p.1.1 r | [] => true)) := by
        change z ∈ support ((fun w => (w.1, (w.2,
            p.2 || (match p.1.2 with | r :: _ => saltKeyed M Salt p.1.1 r | [] => true)))) <$>
          (progGameRunImplTape psf M Salt domainSample pk (.inr msg)).run p.1) at hz
        simp only [support_map, Set.mem_image] at hz
        obtain ⟨w, _, hw⟩ := hz
        simp [← hw]
      simp [this, hp]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] [DecidableEq Salt] [DecidableEq M]
  [SampleableType Salt] in
/-- **Off-collision unfolding of `saltKeyed`.** If the head salt `r` is not yet keyed in the cache
(`saltKeyed cache r = false`), then for every message `m` the random-oracle key `(r, m)` is a cache
miss. This is the side condition the off-bad signing-step agreement consumes: an unkeyed head salt
forces the random-oracle read at `(r, msg)` to be a miss, where the lazy real oracle and the
programmed oracle agree in distribution by `hreg`. -/
lemma saltKeyed_eq_false_iff (cache : (Salt × M →ₒ Range).QueryCache) (r : Salt) :
    saltKeyed M Salt cache r = false ↔ ∀ m : M, cache (r, m) = none := by
  classical
  unfold saltKeyed
  rw [decide_eq_false_iff_not, not_exists]
  exact forall_congr' fun m => by rw [Option.not_isSome_iff_eq_none]

omit [Fintype Salt] [DecidableEq Range] in
/-- **(i) Off-bad signing-step agreement of the two flag-instrumented tape handlers.** On a
*non-empty* tape `r :: tl` whose head salt `r` is not yet keyed (`saltKeyed cache r = false`, so the
collision flag stays `false`), the full signing-step output distributions of `gpvRealImplTapeFlag`
and `progGameRunImplTapeFlag`, started from the off-bad state `((cache, r :: tl), false)`, coincide.

This is the framework `h_agree_good` *signing case* of the identical-until-bad coupling
`gpv_tvDist_tape_runs_le_collisionBound`, lifted from the underlying tape-handler agreement
`evalDist_gpvImplTape_run_sign_miss_eq` (the joint `hreg` substitution): off the collision flag both
flag handlers OR the same `false` collision indicator (the head salt is unkeyed) into the prior
`false` flag, and apply the same flag post-processing to the agreeing underlying signing-step
outputs.  It is the full-output, flag-level generalization of the cache-marginal `gpvStep_agree`,
*pinned* to the concrete flag handlers (no free parameters). -/
theorem evalDist_gpvImplTapeFlag_run_sign_offbad_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (msg : M) (r : Salt) (tl : List Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) (hkey : saltKeyed M Salt cache r = false)
    (hreg : 𝒟[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒟[(gpvRealImplTapeFlag psf M Salt pk sk (.inr msg)).run ((cache, r :: tl), false)]
      = 𝒟[(progGameRunImplTapeFlag psf M Salt domainSample pk (.inr msg)).run
          ((cache, r :: tl), false)] := by
  have hmiss : cache (r, msg) = none := (saltKeyed_eq_false_iff M Salt cache r).1 hkey msg
  rw [gpvRealImplTapeFlag_run_inr, progGameRunImplTapeFlag_run_inr]
  -- The flag post-processing is the same `false`-OR on both sides: simplify it away.
  simp only [Bool.false_or, hkey]
  -- Both reduce to the flag-tagging map applied to the agreeing underlying signing steps.
  exact evalDist_map_eq_of_evalDist_eq
    (evalDist_gpvImplTape_run_sign_miss_eq psf M Salt pk sk domainSample msg r tl cache hmiss hreg)
    _

/-- **Constant-flag map projection of a `false`-tagged output probability.** For the flag-tagging
map `fun p => (p.1, (p.2, F))` (the post-processing common to both flag-instrumented tape handlers
on a single query step), the probability of a `false`-flag output `(u, (s', false))` is exactly the
underlying probability of `(u, s')` when the flag value `F` is `false`, and `0` when `F` is `true`.

This is the bookkeeping that turns the per-query agreement of the *underlying* tape handlers into
the flag-level off-bad agreement `h_agree_good`: where the flag stays `false` the two flagged steps
agree because their underlying steps agree, and where the flag fires the `false`-output probability
is `0` on both sides regardless. -/
lemma probOutput_flagTag_false {α' σ' : Type}
    (m : ProbComp (α' × σ')) (F : Bool) (u : α') (s' : σ') :
    Pr[= (u, (s', false)) |
        ((fun p : α' × σ' => (p.1, (p.2, F))) <$> m : ProbComp (α' × σ' × Bool))]
      = if F = false then Pr[= (u, s') | m] else 0 := by
  classical
  rw [probOutput_map_eq_tsum_ite]
  by_cases hF : F = false
  · subst hF
    rw [if_pos rfl, ← tsum_ite_eq (u, s') (fun x => Pr[= x | m])]
    refine tsum_congr fun x => ?_
    congr 1
    rw [eq_iff_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm, rfl⟩
  · rw [if_neg hF, ENNReal.tsum_eq_zero]
    intro x
    rw [if_neg]
    rw [Prod.ext_iff, Prod.ext_iff]
    rintro ⟨_, _, h3⟩
    exact hF h3.symm

/-! ### Per-query tape↔unified-impl bridges

These lemmas relate one query-step of the tape-consuming impls `gpvRealImplTape` /
`progGameRunImplTape` to one query-step of the unified impls `gpvRealImpl` /
`progGameRunImplNoRec`, all on a common per-query `.run`. They are the analogues of
Fiat–Shamir's per-query relating lemmas. The full `inductionOn (adv.main pk)` factorization
(relating `simulateQ gpvRealImpl` to the front-tape
`drawList ($ᵗ Salt) qSign >>= simulateQ gpvRealImplTape`) and the `drawList`↔`signRunF` step bridge
are carried out in the front-tape factorization below.

First the per-query `.run` unfoldings of the *unified* impls on non-signing queries (the unified
analogues of `gpvRealImplTape_run_unif` / `_read`). Unlike the tape lemmas these are not `rfl`: the
unified real handler is the `∘ₛ`-composition `gpvRealImpl = (outerLift + randomOracle) ∘ₛ
realGameRunImplNoLog`, so each non-signing query reduces through `QueryImpl.compose` /
`realGameRunImplNoLog`'s query re-emission. -/

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImpl` on a uniform query.** The cache is untouched: the unified
real handler re-emits the public-randomness query through `realGameRunImplNoLog` and the outer
public-randomness lift forwards it to the bare `unifSpec.query n`, pairing the cache back unchanged.
-/
lemma gpvRealImpl_run_unif (pk : PK) (sk : SK) (n : unifSpec.Domain)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImpl psf hr M Salt pk sk (.inl (.inl n))).run cache =
      (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _) := rfl

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImpl` on a random-oracle read query.** The unified real handler
re-emits the random-oracle query through `realGameRunImplNoLog`, and the outer `randomOracle`
summand runs the lazy random-oracle step on the cache component. -/
lemma gpvRealImpl_run_read (pk : PK) (sk : SK) (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc))).run cache =
      (randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache := by
  simp [gpvRealImpl, QueryImpl.compose, realGameRunImplNoLog, HAdd.hAdd, QueryImpl.add]

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImpl` on a signing query (the `∘ₛ`/`liftM` unfold).** The
unified real handler runs the real GPV signing body of `realGameRunImplNoLog` — `do r ← $ᵗ Salt; c ←
query (r, msg); s ← trapdoorSample c; pure (r, s)` — through the outer public-randomness-lift `+
randomOracle` simulation. The inline salt draw `r ← $ᵗ Salt` and the trapdoor draw pass through the
left (public-randomness) lift unchanged, and the random-oracle query `query (r, msg)` is answered by
the outer lazy `randomOracle` on the cache component, yielding the explicit inline sign body: draw a
fresh salt `r`, run the lazy random-oracle step at `(r, msg)`, draw the trapdoor preimage, and
return `((r, s), cache')`.

This is the GPV analogue of the FS deferred-sign-step body unfolding; it resolves the `∘ₛ`/`liftM`
indirection of `gpvRealImpl = (outerLift + randomOracle) ∘ₛ realGameRunImplNoLog` on the signing
query. It is *pinned* to the concrete `gpvRealImpl` and is a pure structural unfold (no salt
front-loading, no distributional coupling), via the per-action `simulateQ` rungs
(`simulateQ_add_liftM_left` / `simulateQ_liftTarget` / `ofLift_eq_id'` for the lifted draws) and
`gpvRealImpl_run_read` for the random-oracle query. -/
lemma gpvRealImpl_run_sign (pk : PK) (sk : SK) (msg : M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (gpvRealImpl psf hr M Salt pk sk (Sum.inr msg)).run cache =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        let s ← psf.trapdoorSample pk sk p.1
        pure ((r, s), p.2)) := by
  change (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) +
      (randomOracle : QueryImpl (Salt × M →ₒ Range)
        (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
      ((GPVHashAndSign psf hr M Salt).sign pk sk msg)).run cache = _
  simp only [GPVHashAndSign, simulateQ_bind, StateT.run_bind,
    QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, QueryImpl.ofLift_eq_id',
    simulateQ_id', StateT.run_monadLift, simulateQ_pure, StateT.run_pure,
    bind_assoc, pure_bind]
  refine bind_congr (fun x => ?_)
  congr 1
  exact gpvRealImpl_run_read psf hr M Salt pk sk (x, msg) cache

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a uniform query.** The cache is untouched. -/
lemma progGameRunImplNoRec_run_unif (domainSample : PK → ProbComp Domain) (pk : PK)
    (n : unifSpec.Domain) (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl n))).run cache =
      (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _) := rfl

open Classical in
omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a random-oracle read query.** On a cache hit
the recorded value is returned; on a miss the answer is programmed to
`psf.eval pk (domainSample pk)` and recorded in the cache. The tape (in the tape impl) is replaced
here by the bare cache. -/
lemma progGameRunImplNoRec_run_read (domainSample : PK → ProbComp Domain) (pk : PK) (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc))).run cache =
      (match cache mc with
        | some v => pure (v, cache)
        | none =>
            (fun sd : Domain => (psf.eval pk sd, cache.cacheQuery mc (psf.eval pk sd))) <$>
              (domainSample pk : ProbComp Domain)) := by
  cases h : cache mc <;>
    simp [progGameRunImplNoRec, HAdd.hAdd, QueryImpl.add, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_monadLift, h, map_eq_bind_pure_comp, Function.comp]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a signing query.** The programmed (simulator)
signing handler draws a fresh salt `r ← $ᵗ Salt`, forward-samples a short preimage `s ← domainSample
pk`, programs the random-oracle cache point `(r, msg) ↦ psf.eval pk s`, and returns `(r, s)` (the
preimage record is dropped in the record-free `progGameRunImplNoRec` model). The `.run cache` thus
yields the explicit inline programmed sign body: draw `r`, draw `s`, and pair `(r, s)` with the
programmed cache `cache.cacheQuery (r, msg) (psf.eval pk s)`.

This is the programmed dual of `gpvRealImpl_run_sign`; it is *pinned* to the concrete
`progGameRunImplNoRec` signing handler and is a pure structural unfold. -/
lemma progGameRunImplNoRec_run_sign (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (cache : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (Sum.inr msg)).run cache =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let s ← (domainSample pk : ProbComp Domain)
        pure ((r, s), cache.cacheQuery (r, msg) (psf.eval pk s))) := by
  simp [progGameRunImplNoRec, HAdd.hAdd, QueryImpl.add, StateT.run_bind, StateT.run_get,
    StateT.run_set, StateT.run_monadLift, map_eq_bind_pure_comp, Function.comp, bind_assoc,
    pure_bind]

omit [Fintype Salt] in
/-- **Tier-1 (uniform) tape↔unified bridge — real side.** One uniform query-step of the tape impl
`gpvRealImplTape` equals the corresponding `gpvRealImpl` step with the salt tape carried through
unchanged: both forward the bare `unifSpec.query n` and leave the cache (resp. cache and tape)
untouched. This is the FS template's trivial per-query relating lemma; the tape is a passive
passenger on a uniform query. -/
lemma gpvRealImplTape_run_unif_eq_gpvRealImpl (pk : PK) (sk : SK) (n : unifSpec.Domain)
    (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inl n))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl (.inl n))).run cache := by
  rw [gpvRealImplTape_run_unif, gpvRealImpl_run_unif]; rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Tier-1 (uniform) tape↔unified bridge — programmed side.** One uniform query-step of the
programmed tape impl `progGameRunImplTape` equals the corresponding `progGameRunImplNoRec` step with
the salt tape carried through unchanged. -/
lemma progGameRunImplTape_run_unif_eq_progGameRunImplNoRec (domainSample : PK → ProbComp Domain)
    (pk : PK) (n : unifSpec.Domain) (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl n))).run cache := by
  rw [progGameRunImplTape_run_unif, progGameRunImplNoRec_run_unif]; rfl

omit [Fintype Salt] in
/-- **Tier-2 (random-oracle read) tape↔unified bridge — real side.** One random-oracle read
query-step of the tape impl `gpvRealImplTape` equals the corresponding `gpvRealImpl` step with the
salt tape carried through unchanged: both run the *same* lazy `randomOracle` step on the cache
component (`gpvRealImpl` re-emits the read query through `realGameRunImplNoLog` and the outer
`randomOracle` summand answers it), leaving the tape a passive passenger. -/
lemma gpvRealImplTape_run_read_eq_gpvRealImpl (pk : PK) (sk : SK) (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc))).run cache := by
  rw [gpvRealImplTape_run_read, gpvRealImpl_run_read]; rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Tier-2 (random-oracle read) tape↔unified bridge — programmed side.** One random-oracle read
query-step of the programmed tape impl `progGameRunImplTape` equals the corresponding
`progGameRunImplNoRec` step with the salt tape carried through unchanged: on a cache hit both return
the recorded value, on a miss both program `psf.eval pk (domainSample pk)` and record it, leaving
the tape untouched. -/
lemma progGameRunImplTape_run_read_eq_progGameRunImplNoRec (domainSample : PK → ProbComp Domain)
    (pk : PK) (mc : Salt × M) (cache : (Salt × M →ₒ Range).QueryCache) (tape : List Salt) :
    (progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run (cache, tape) =
      (fun p => (p.1, (p.2, tape))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc))).run cache := by
  rw [progGameRunImplTape_run_read, progGameRunImplNoRec_run_read]
  cases h : cache mc <;> simp [h, Functor.map_map]

/-! ### Front salt-tape factorization

With the per-query tape↔unified bridges in place, the front-tape factorization of each
game run is the `OracleComp.inductionOn (adv.main pk)` mirroring the worked Fiat–Shamir headline
`FiatShamirWithAbort.evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`. Each game run distributes
as a single front draw block `OracleComp.drawList ($ᵗ Salt) qSign` of fresh signing salts followed
by the corresponding *tape-consuming* run (`gpvRealImplTape` / `progGameRunImplTape`) reading each
signing query's salt off the tape head, with the spent tape suffix projected away on output.

Unlike the Fiat–Shamir instance (where each signing query consumes a `maxAttempts`-block), every GPV
signing query consumes *exactly one* salt off the tape head, so the front block has length `qSign`
and the per-signing-query split peels off a single leading salt (`drawList ($ᵗ Salt) 1`). The
non-signing (uniform / random-oracle-read) steps consume *zero* tape and commute trivially past the
front block (the generic answer-irrelevant commute
`OracleComp.DeferredSampling.evalDist_step_commute_tape`, fed by the tape↔unified
bridges). -/

omit [Fintype Salt] [DecidableEq Salt] in
/-- **Front salt-tape splits as a leading salt followed by the remaining block.** Drawing a
`drawList ($ᵗ Salt) (n + 1)` front block is the same as drawing one leading salt and then the
remaining `n`-block, consing the leading salt onto the front. This is the GPV (one-salt-per-signing
step) analogue of `FiatShamirWithAbort.drawList_commit_add` at `m = 1`; it peels the head salt that
a single signing query consumes off the over-provisioned front tape. -/
lemma drawList_salt_succ (n : ℕ) :
    OracleComp.drawList ($ᵗ Salt : ProbComp Salt) (n + 1) =
      (do let r ← ($ᵗ Salt : ProbComp Salt)
          let tl ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) n
          pure (r :: tl)) := by
  rfl

omit [Fintype Salt] in
/-- **Real-side signing-step front-tape commute (the crux inductive step).** One real signing
query-step of the unified handler `gpvRealImpl`, composed with the deferred continuation, factors as
a single front draw block `drawList ($ᵗ Salt) (qSrem + 1)` of fresh salts followed by the
tape-consuming `gpvRealImplTape` signing step (reading the head salt) and the tape-threaded
continuation.

The genuine framework content: the leading salt is peeled off the front block by
`drawList_salt_succ` and fed to the tape signing step (consuming the tape head `r :: tl`); the
per-body cache transition of that tape step is exactly the unified `gpvRealImpl` signing step at the
front-loaded salt `r` (the per-body splice `evalDist_gpvRealImplTape_sign_cache_eq_gpvStepReal`
reformulated against `gpvRealImpl`); and the continuation's `qSrem`-block (supplied by the inductive
hypothesis `hcont`) commutes past the body via the i.i.d. resampling commute `evalDist_bind_comm`.

It is *pinned* to the concrete `gpvRealImpl` / `gpvRealImplTape` handlers and is the signing case of
the real-side front-tape factorization headline
`evalDist_gpvRealImpl_eq_drawList_gpvRealImplTape`. -/
theorem evalDist_gpvSignStep_commute_real {γ : Type} (pk : PK) (sk : SK) (msg : M)
    (cache : (Salt × M →ₒ Range).QueryCache) (qSrem : ℕ)
    (ob : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (hcont : ∀ (a : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range
          (Sum.inr msg))
        (c' : (Salt × M →ₒ Range).QueryCache),
      𝒟[(simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob a)).run c'] =
        𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tape =>
            (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob a)).run (c', tape)]) :
    𝒟[(gpvRealImpl psf hr M Salt pk sk (Sum.inr msg)).run cache >>= fun p =>
        (simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob p.1)).run p.2] =
      𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) (qSrem + 1) >>= fun tape =>
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
            ((gpvRealImplTape psf M Salt pk sk (Sum.inr msg)).run (cache, tape) >>= fun p =>
              (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2)] := by
  -- Peel the leading salt off both sides: the LHS inline sign body (via `gpvRealImpl_run_sign`)
  -- and the RHS front draw block (via `drawList_salt_succ`) both begin with `r ← $ᵗ Salt`.
  rw [gpvRealImpl_run_sign, drawList_salt_succ]
  simp only [bind_assoc, map_bind, pure_bind]
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun r => ?_)
  -- Both sides reduce to a common middle form: draw the `qSrem` salt tape, then the random-oracle
  -- answer and the trapdoor preimage `s`, then run the tape continuation `ob (r, s)`.
  -- LHS reaches it by applying `hcont` under the two leading draws and commuting the front block to
  -- the head; RHS by flattening the consumed tape head (`hflat`, no reordering).
  trans 𝒟[do
      let tl ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem
      let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
      let s ← psf.trapdoorSample pk sk p.1
      (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
        (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)]
  · -- LHS → middle: rewrite the unified continuation by `hcont` under the two leading draws, then
    -- commute the resulting `drawList qSrem` block to the front past the answer-irrelevant draws.
    rw [show 𝒟[(randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache >>= fun p =>
          psf.trapdoorSample pk sk p.1 >>= fun s =>
            (simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob (r, s))).run p.2]
        = 𝒟[(randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache >>= fun p =>
          psf.trapdoorSample pk sk p.1 >>= fun s =>
            OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tl =>
              (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
                (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)]
      from OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun p =>
        OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun s => hcont (r, s) p.2))]
    -- Commute the innermost `drawList qSrem` past the trapdoor draw (under the random-oracle bind).
    rw [show 𝒟[(randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache >>= fun p =>
          psf.trapdoorSample pk sk p.1 >>= fun s =>
            OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tl =>
              (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
                (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)]
        = 𝒟[(randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache >>= fun p =>
          OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tl =>
            psf.trapdoorSample pk sk p.1 >>= fun s =>
              (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
                (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)]
      from OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun p =>
        OracleComp.DeferredSampling.evalDist_bind_comm
          (psf.trapdoorSample pk sk p.1)
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun s tl =>
            (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
              (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)))]
    -- Commute the `drawList qSrem` past the random-oracle draw to the front.
    rw [OracleComp.DeferredSampling.evalDist_bind_comm
      ((randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache)
      (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
      (fun p tl => psf.trapdoorSample pk sk p.1 >>= fun s =>
        (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
          (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl))]
  · -- middle → RHS: flatten the consumed tape head `r :: tl` (no reordering needed).
    symm
    have hflat : ∀ (tl : List Salt),
        ((do
            let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
            let s ← psf.trapdoorSample pk sk p.1
            pure (((r, s), p.2, tl) :
              (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × List Salt))) >>=
          fun a => (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) =>
              (pp.1, pp.2.1)) <$>
            (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob a.1)).run a.2)
          = (do
            let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
            let s ← psf.trapdoorSample pk sk p.1
            (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
              (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob (r, s))).run (p.2, tl)) := by
      intro tl; simp only [bind_assoc, pure_bind]
    simp only [gpvRealImplTape_run_sign_cons, map_bind, map_pure]
    exact OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
      (fun tl => congrArg _ (hflat tl))

omit [Fintype Salt] in
/-- **Real-side front salt-tape factorization (the Fiat–Shamir-template headline, real side).** By
`OracleComp.inductionOn` on the adversary computation `oa`, the unified real run distributes as a
single front draw block `drawList ($ᵗ Salt) qSrem` of fresh signing salts followed by the
tape-consuming real run `gpvRealImplTape`, the spent-tape suffix projected away on output:

`𝒟[(simulateQ gpvRealImpl oa).run cache]`
`  = 𝒟[drawList ($ᵗ Salt) qSrem >>= fun tape => (·.1, ·.2.1) <$> (simulateQ gpvRealImplTape oa).run`
`        (cache, tape)]`,

where `qSrem` bounds the number of signing queries of `oa` (the `(· matches .inr _)` component of
`signHashQueryBound`). At a **pure** step the front block is value-irrelevant and discarded
(never-failing-prefix discard via `OracleComp.probFailure_drawList`); at a **uniform /
random-oracle-read** step the answer is independent of the tape so the front block commutes
trivially past the step (`OracleComp.DeferredSampling.evalDist_step_commute_tape`, fed by the
tape↔unified bridges); at a **signing** step the leading salt is peeled off and consumed by
the tape head (`evalDist_gpvSignStep_commute_real`).

It is *pinned* to the concrete `gpvRealImpl` / `gpvRealImplTape` handlers; together with the
prog-side dual it puts both game runs in the front-tape form the coupling factors through. -/
theorem evalDist_gpvRealImpl_eq_drawList_gpvRealImplTape {γ : Type} (pk : PK) (sk : SK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (cache : (Salt × M →ₒ Range).QueryCache),
        𝒟[(simulateQ (gpvRealImpl psf hr M Salt pk sk) oa).run cache] =
          𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tape =>
              (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
                (simulateQ (gpvRealImplTape psf M Salt pk sk) oa).run (cache, tape)] := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ cache
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
        (OracleComp.probFailure_drawList _ _)]
  | query_bind t ob ih =>
      intro qSrem hQ cache
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rcases t with (n | mc) | msg
      · -- UNIFORM: answer independent of the tape; commute the front block past the step.
        have hqs : (if (match (Sum.inl (Sum.inl n) :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show (gpvRealImpl psf hr M Salt pk sk (Sum.inl (Sum.inl n))).run cache
              = (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _)
            from gpvRealImpl_run_unif psf hr M Salt pk sk n cache]
        rw [show (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              ((gpvRealImplTape psf M Salt pk sk (Sum.inl (Sum.inl n))).run (cache, tape)
                >>= fun p =>
                  (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (((fun p : unifSpec.Range n × (Salt × M →ₒ Range).QueryCache =>
                  (p.1, (p.2, tape))) <$>
                  ((fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _)))
                >>= fun p =>
                  (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2))
            from by
              funext tape
              rw [gpvRealImplTape_run_unif_eq_gpvRealImpl psf hr M Salt pk sk n cache tape,
                gpvRealImpl_run_unif]
              rfl]
        exact OracleComp.DeferredSampling.evalDist_step_commute_tape
          ((fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _))
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1))
          (fun a c' => (simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob a)).run c')
          (fun a st => (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob a)).run st)
          (fun a c' => ih a qSrem (hQ2 a) c')
      · -- READ: answer is the lazy RO step, independent of the tape; same commute.
        have hqs : (if (match (Sum.inl (Sum.inr mc) :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show (gpvRealImpl psf hr M Salt pk sk (Sum.inl (Sum.inr mc))).run cache
              = (randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache
            from gpvRealImpl_run_read psf hr M Salt pk sk mc cache]
        rw [show (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              ((gpvRealImplTape psf M Salt pk sk (Sum.inl (Sum.inr mc))).run (cache, tape)
                >>= fun p =>
                  (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (((fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, tape))) <$>
                  (randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache)
                >>= fun p =>
                  (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob p.1)).run p.2))
            from by
              funext tape
              rw [gpvRealImplTape_run_read_eq_gpvRealImpl psf hr M Salt pk sk mc cache tape,
                gpvRealImpl_run_read]
              rfl]
        exact OracleComp.DeferredSampling.evalDist_step_commute_tape
          ((randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache)
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1))
          (fun a c' => (simulateQ (gpvRealImpl psf hr M Salt pk sk) (ob a)).run c')
          (fun a st => (simulateQ (gpvRealImplTape psf M Salt pk sk) (ob a)).run st)
          (fun a c' => ih a qSrem (hQ2 a) c')
      · -- SIGN: peel the leading salt; consume the tape head.
        have hpos : 0 < qSrem := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        clear hQ1
        have hqs : (if (match (Sum.inr msg :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem - 1 := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show qSrem = (qSrem - 1) + 1 from by omega]
        exact evalDist_gpvSignStep_commute_real psf hr M Salt pk sk msg cache (qSrem - 1) ob
          (fun a c' => ih a (qSrem - 1) (hQ2 a) c')

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Programmed-side signing-step front-tape commute (the crux inductive step, programmed dual).**
One programmed signing query-step of the unified handler `progGameRunImplNoRec`, composed with the
deferred continuation, factors as a single front draw block `drawList ($ᵗ Salt) (qSrem + 1)` of
fresh salts followed by the tape-consuming `progGameRunImplTape` signing step (reading the head
salt) and the tape-threaded continuation.

This is the programmed dual of `evalDist_gpvSignStep_commute_real`: the leading salt is peeled off
the front block and fed to the tape signing step (consuming the tape head `r :: tl`); the per-body
cache transition of that tape step is the unified `progGameRunImplNoRec` signing step at the
front-loaded salt `r` (the per-body splice `evalDist_progGameRunImplTape_sign_cache_eq_gpvStepProg`
reformulated against `progGameRunImplNoRec`); and the continuation's `qSrem`-block commutes past the
body via the i.i.d. resampling commute `evalDist_bind_comm`.

It is *pinned* to the concrete `progGameRunImplNoRec` / `progGameRunImplTape` handlers and is the
signing case of the prog-side headline
`evalDist_progGameRunImplNoRec_eq_drawList_progGameRunImplTape`. -/
theorem evalDist_gpvSignStep_commute_prog {γ : Type} (domainSample : PK → ProbComp Domain)
    (pk : PK) (msg : M) (cache : (Salt × M →ₒ Range).QueryCache) (qSrem : ℕ)
    (ob : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (hcont : ∀ (a : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range
          (Sum.inr msg))
        (c' : (Salt × M →ₒ Range).QueryCache),
      𝒟[(simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob a)).run c'] =
        𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tape =>
            (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob a)).run (c', tape)]) :
    𝒟[(progGameRunImplNoRec psf M Salt domainSample pk (Sum.inr msg)).run cache >>= fun p =>
        (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob p.1)).run p.2] =
      𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) (qSrem + 1) >>= fun tape =>
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
            ((progGameRunImplTape psf M Salt domainSample pk (Sum.inr msg)).run (cache, tape)
              >>= fun p =>
              (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2)] := by
  -- Peel the leading salt off both sides: the LHS inline sign body (via
  -- `progGameRunImplNoRec_run_sign`) and the RHS front draw block (via `drawList_salt_succ`).
  rw [progGameRunImplNoRec_run_sign, drawList_salt_succ]
  simp only [bind_assoc, map_bind, pure_bind]
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun r => ?_)
  -- Both sides reduce to the drawList-outermost middle form. LHS: apply `hcont` under the
  -- `domainSample` draw, then commute the resulting `drawList qSrem` block to the front. RHS:
  -- flatten the consumed tape head (no reordering).
  trans 𝒟[do
      let tl ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem
      let s ← (domainSample pk : ProbComp Domain)
      (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
        (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob (r, s))).run
          (cache.cacheQuery (r, msg) (psf.eval pk s), tl)]
  · -- LHS → middle: rewrite the unified continuation by `hcont` under the `domainSample` draw,
    -- then commute the `drawList qSrem` block to the front past the `domainSample` draw.
    rw [show 𝒟[(domainSample pk : ProbComp Domain) >>= fun s =>
          (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob (r, s))).run
            (cache.cacheQuery (r, msg) (psf.eval pk s))]
        = 𝒟[(domainSample pk : ProbComp Domain) >>= fun s =>
          OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tl =>
            (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
              (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob (r, s))).run
                (cache.cacheQuery (r, msg) (psf.eval pk s), tl)]
      from OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
        (fun s => hcont (r, s) (cache.cacheQuery (r, msg) (psf.eval pk s)))]
    rw [OracleComp.DeferredSampling.evalDist_bind_comm
      (domainSample pk : ProbComp Domain)
      (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
      (fun s tl =>
        (fun pp : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (pp.1, pp.2.1)) <$>
          (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob (r, s))).run
            (cache.cacheQuery (r, msg) (psf.eval pk s), tl))]
  · -- middle → RHS: flatten the consumed tape head `r :: tl` (no reordering needed).
    symm
    refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun tl => ?_)
    rw [progGameRunImplTape_run_sign_cons]
    exact congrArg _ (bind_map_left
      (fun sd => ((r, sd), cache.cacheQuery (r, msg) (psf.eval pk sd), tl))
      (domainSample pk)
      (fun a => (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
        (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob a.1)).run a.2))

omit [Fintype Salt] [DecidableEq Range] [SampleableType Range] in
/-- **Prog-side front salt-tape factorization (the Fiat–Shamir-template headline, prog side).**
By `OracleComp.inductionOn` on the adversary computation `oa`, the unified programmed run
distributes as a single front draw block `drawList ($ᵗ Salt) qSrem` of fresh signing salts followed
by the tape-consuming programmed run `progGameRunImplTape`, the spent-tape suffix projected away on
output.

This is the programmed dual of `evalDist_gpvRealImpl_eq_drawList_gpvRealImplTape`: pure step
discards the value-irrelevant front block; uniform / random-oracle-read steps commute the front
block past the answer-irrelevant step (via the tape↔unified bridges and
`OracleComp.DeferredSampling.evalDist_step_commute_tape`); the signing step peels off and consumes
the leading salt (`evalDist_gpvSignStep_commute_prog`). It is *pinned* to the concrete
`progGameRunImplNoRec` / `progGameRunImplTape` handlers. -/
theorem evalDist_progGameRunImplNoRec_eq_drawList_progGameRunImplTape {γ : Type}
    (domainSample : PK → ProbComp Domain) (pk : PK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (cache : (Salt × M →ₒ Range).QueryCache),
        𝒟[(simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) oa).run cache] =
          𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem >>= fun tape =>
            (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (simulateQ (progGameRunImplTape psf M Salt domainSample pk) oa).run
                (cache, tape)] := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ cache
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
        (OracleComp.probFailure_drawList _ _)]
  | query_bind t ob ih =>
      intro qSrem hQ cache
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rcases t with (n | mc) | msg
      · -- UNIFORM: answer independent of the tape; commute the front block past the step.
        have hqs : (if (match (Sum.inl (Sum.inl n) :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show (progGameRunImplNoRec psf M Salt domainSample pk (Sum.inl (Sum.inl n))).run cache
              = (fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _)
            from progGameRunImplNoRec_run_unif psf M Salt domainSample pk n cache]
        rw [show (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              ((progGameRunImplTape psf M Salt domainSample pk (Sum.inl (Sum.inl n))).run
                  (cache, tape) >>= fun p =>
                  (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (((fun p : unifSpec.Range n × (Salt × M →ₒ Range).QueryCache =>
                  (p.1, (p.2, tape))) <$>
                  ((fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _)))
                >>= fun p =>
                  (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2))
            from by
              funext tape
              rw [progGameRunImplTape_run_unif_eq_progGameRunImplNoRec psf M Salt domainSample pk n
                  cache tape,
                progGameRunImplNoRec_run_unif]
              rfl]
        exact OracleComp.DeferredSampling.evalDist_step_commute_tape
          ((fun u => (u, cache)) <$> (unifSpec.query n : ProbComp _))
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1))
          (fun a c' => (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob a)).run c')
          (fun a st => (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob a)).run st)
          (fun a c' => ih a qSrem (hQ2 a) c')
      · -- READ: answer is the programmed RO step, independent of the tape; same commute.
        have hqs : (if (match (Sum.inl (Sum.inr mc) :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              ((progGameRunImplTape psf M Salt domainSample pk (Sum.inl (Sum.inr mc))).run
                  (cache, tape) >>= fun p =>
                  (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1)) <$>
              (((fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, (p.2, tape))) <$>
                (progGameRunImplNoRec psf M Salt domainSample pk (Sum.inl (Sum.inr mc))).run cache)
                >>= fun p =>
                  (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob p.1)).run p.2))
            from by
              funext tape
              rw [progGameRunImplTape_run_read_eq_progGameRunImplNoRec psf M Salt domainSample pk mc
                  cache tape]
              rfl]
        exact OracleComp.DeferredSampling.evalDist_step_commute_tape
          ((progGameRunImplNoRec psf M Salt domainSample pk (Sum.inl (Sum.inr mc))).run cache)
          (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSrem)
          (fun p : γ × ((Salt × M →ₒ Range).QueryCache × List Salt) => (p.1, p.2.1))
          (fun a c' => (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (ob a)).run c')
          (fun a st => (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (ob a)).run st)
          (fun a c' => ih a qSrem (hQ2 a) c')
      · -- SIGN: peel the leading salt; consume the tape head.
        have hpos : 0 < qSrem := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        clear hQ1
        have hqs : (if (match (Sum.inr msg :
              ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem - 1 := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rw [show qSrem = (qSrem - 1) + 1 from by omega]
        exact evalDist_gpvSignStep_commute_prog psf M Salt domainSample pk msg cache (qSrem - 1)
          ob (fun a c' => ih a (qSrem - 1) (hQ2 a) c')

open Classical in
omit [Fintype Salt] in
/-- **Real game-run front-tape factorization (pinned bridge).**

The *pinned* real EUF-CMA game run `realGameRun … adv pk sk` equals a front salt-tape draw
`drawList ($ᵗ Salt) qSign` followed by the tape-consuming real run of `adv.main pk`, with the salt
tape projected away. This is the bridge from the actual game run to the tape-consuming
`gpvRealImplTape` vehicle: it chains the single-impl normalization
`realGameRun_eq_run'_implReal` (`realGameRun … = 𝒟[(simulateQ gpvRealImpl (adv.main pk)).run' ∅]`)
with the front-tape factorization
`evalDist_gpvRealImpl_eq_drawList_gpvRealImplTape`
(instantiated at the empty cache, with the signing-query bound supplied by `hQ.1`).

The `StateT.run'` of the single-impl form is `Prod.fst <$> StateT.run`, so the front-tape
factorization — whose tape side is `(·.1, ·.2.1) <$> (… .run (∅, tape))` — composes to the same
`Prod.fst` projection once the (discarded) salt-tape component is dropped. This bridge front-loads
every adaptively-issued signing salt of the real game into one front block, leaving a tape-consuming
run; it is the FS-template factorization pinned to the *actual* game run, and is the prerequisite
for the `drawList`↔`signRunF` step bridge. -/
theorem realGameRun_eq_drawList_gpvRealImplTape (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    realGameRun psf hr M Salt adv pk sk =
      𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign >>= fun tape =>
          (fun p : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.1) <$>
            (simulateQ (gpvRealImplTape psf M Salt pk sk) (adv.main pk)).run
              ((∅ : (Salt × M →ₒ Range).QueryCache), tape)] := by
  classical
  rw [realGameRun_eq_run'_implReal]
  rw [StateT.run']
  refine (evalDist_map_eq_of_evalDist_eq
    (evalDist_gpvRealImpl_eq_drawList_gpvRealImplTape psf hr M Salt pk sk (adv.main pk) qSign hQ.1
      (∅ : (Salt × M →ₒ Range).QueryCache)) Prod.fst).trans ?_
  rw [map_bind]
  simp only [Functor.map_map]

open Classical in
omit [Fintype Salt] in
/-- **Programmed game-run front-tape factorization (pinned bridge).**

The *pinned* randomized sign-then-hash game run `progGameRun … adv domainSample pk` equals a front
salt-tape draw `drawList ($ᵗ Salt) qSign` followed by the tape-consuming programmed run of
`adv.main pk`, with the salt tape projected away. The programmed dual of
`realGameRun_eq_drawList_gpvRealImplTape`: it chains the record-free normalization
`progGameRun_eq_run'_implNoRec` with the programmed front-tape factorization
`evalDist_progGameRunImplNoRec_eq_drawList_progGameRunImplTape`
(signing bound from `hQ.1`). Together
the two bridges put both pinned game runs into the identical front-tape
`drawList ($ᵗ Salt) qSign >>= (tape-consuming run)` shape, the prerequisite for the
`drawList`↔`signRunF` step bridge. -/
theorem progGameRun_eq_drawList_progGameRunImplTape (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    progGameRun psf hr M Salt adv domainSample pk =
      𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign >>= fun tape =>
          (fun p : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × List Salt) => p.1) <$>
            (simulateQ (progGameRunImplTape psf M Salt domainSample pk) (adv.main pk)).run
              ((∅ : (Salt × M →ₒ Range).QueryCache), tape)] := by
  classical
  rw [progGameRun_eq_run'_implNoRec]
  rw [StateT.run']
  refine (evalDist_map_eq_of_evalDist_eq
    (evalDist_progGameRunImplNoRec_eq_drawList_progGameRunImplTape psf M Salt domainSample pk
      (adv.main pk) qSign hQ.1 (∅ : (Salt × M →ₒ Range).QueryCache)) Prod.fst).trans ?_
  rw [map_bind]
  simp only [Functor.map_map]

/-! ## Direct front-tape derivation of the Step-1 TV bound

The pieces below derive `gpv_tvDist_real_programmed_le_collisionBound` *directly* from the
front-tape factorization (`realGameRun_eq_drawList_gpvRealImplTape` /
`progGameRun_eq_drawList_progGameRunImplTape`), via the direct front-tape coupling
`gpv_tvDist_tape_runs_le_collisionBound`.

After the front-tape factorization both pinned game runs are `drawList ($ᵗ Salt) qSign` followed by
the tape-consuming run of `adv.main pk`. The TV distance is then bounded by:

* **(C) data processing** — `tvDist_drawList_bind_le` reduces the TV of the two factored runs to the
  expectation over the front salt tape of the per-tape TV distance (`tvDist_bind_left_le`).
* **(A) per-tape identical-until-bad** — `gpv_tvDist_tape_runs_le_collisionBound`: the tape-averaged
  TV between the real and programmed tape-consuming runs of `adv.main pk` over the front tape is
  bounded *directly* by `(collisionBound …).toReal`. The per-tape bad event is a fresh tape salt
  hitting the actual running random-oracle cache; its salt-averaged probability telescopes to
  `collisionBound`.

The salt-tape birthday infrastructure (`tapeCheck`, `drawList_tapeCheck_eq_saltSeq`,
`probEvent_tapeCheck_drawList_le_collisionBound`) records the explicit-list form of the
salt-averaged `saltSeq` telescope; it is the analytic tool the run-level collision-flag charge of
`(A)` reduces to via the flag-instrumented inductive coupling. -/

/-- **Salt-tape collision check.** `tapeCheck c n tape` is the explicit-list analogue of the
salt-averaged `saltSeq` disjunction: it reports `true` iff some head salt of the front `n`-block
tape `tape` lands in its recorded cache slice `c j`. The head salt of an `(n + 1)`-block is checked
against `c n` (mirroring `saltSeq`'s leading `decide (r ∈ c n)`), and the tail recurses on the
remaining `n`-block. On a tape shorter than `n` the missing entries are treated as non-colliding
(`false`), which never occurs for tapes drawn by `drawList ($ᵗ Salt) n`. -/
def tapeCheck (c : ℕ → Finset Salt) : ℕ → List Salt → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | n + 1, r :: tl => decide (r ∈ c n) || tapeCheck c n tl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **The tape-check process equals the salt-averaged `saltSeq` process.** Drawing a front salt tape
`drawList ($ᵗ Salt) n` and reporting its `tapeCheck` collision flag is the *same computation* as the
salt-averaged `saltSeq c n`: both draw `n` fresh uniform salts and OR together, at each step `j`,
the indicator that the `j`-th salt lands in `c j`. Proved by induction on `n`, matching `drawList`'s
head-cons recursion against `saltSeq`'s leading-draw recursion. -/
theorem drawList_tapeCheck_eq_saltSeq (c : ℕ → Finset Salt) (n : ℕ) :
    (do let tape ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) n
        pure (tapeCheck Salt c n tape)) = saltSeq (Salt := Salt) c n := by
  induction n with
  | zero => simp [OracleComp.drawList, tapeCheck, saltSeq]
  | succ n ih =>
      rw [OracleComp.drawList, saltSeq]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun r => ?_
      rw [← ih]
      simp only [bind_assoc, pure_bind, tapeCheck]

omit [DecidableEq Range] [SampleableType Range] in
/-- **(B) drawList salt-tape birthday bound.** The probability that a front salt tape drawn by
`drawList ($ᵗ Salt) qSign` reports a `tapeCheck` collision is bounded by
`collisionBound Salt qSign qHash`, whenever the recorded cache slices satisfy the growth bound
`card (c j) ≤ j + qHash`.

This is the front-tape analogue of `probEvent_saltSeq_le_collisionBound`: it transports the
salt-averaged telescope to the explicit front-tape vehicle via `drawList_tapeCheck_eq_saltSeq`. It
is the birthday term charged by the data-processing reduction `(C)` against the per-tape
identical-until-bad coupling `(A)`. -/
theorem probEvent_tapeCheck_drawList_le_collisionBound (qSign qHash : ℕ)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash) :
    Pr[(· = true) | (do let tape ← OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign
                        pure (tapeCheck Salt c qSign tape))]
      ≤ collisionBound Salt qSign qHash := by
  rw [drawList_tapeCheck_eq_saltSeq]
  exact probEvent_saltSeq_le_collisionBound Salt qSign qHash c hcache

omit [DecidableEq Salt] [Fintype Salt] in
/-- **(C) Data-processing reduction for the factored game runs.** Given that both pinned game runs
have been put into the front-tape form `realGameRun = 𝒟[drawList ($ᵗ Salt) qSign >>= freal]` and
`progGameRun = 𝒟[drawList ($ᵗ Salt) qSign >>= fprog]` (supplied by the bridges
`realGameRun_eq_drawList_gpvRealImplTape` / `progGameRun_eq_drawList_progGameRunImplTape`), the TV
distance between the game runs is bounded by the expectation, over the front salt tape, of the
per-tape TV distance between the two tape-consuming runs.

This is the front-tape instance of the generic data-processing bound `tvDist_bind_left_le`: binding
two continuations over a common base computation (the salt tape `drawList ($ᵗ Salt) qSign`) costs at
most the tape-averaged per-fibre TV distance. It reduces the run-level coupling to the per-tape
identical-until-bad coupling `(A)`, whose tape-averaged charge is bounded by the birthday term
`(B)`. -/
theorem tvDist_drawList_bind_le {β : Type} (qSign : ℕ) (freal fprog : List Salt → ProbComp β)
    (realRun progRun : SPMF β)
    (hreal : realRun = 𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign >>= freal])
    (hprog : progRun = 𝒟[OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign >>= fprog]) :
    SPMF.tvDist realRun progRun
      ≤ ∑' tape : List Salt,
          Pr[= tape | OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign].toReal *
            tvDist (freal tape) (fprog tape) := by
  subst hreal hprog
  exact tvDist_bind_left_le (OracleComp.drawList ($ᵗ Salt : ProbComp Salt) qSign) freal fprog

omit [DecidableEq Range] [DecidableEq Salt] [SampleableType Salt] [Fintype Salt] in
/-- **First marginal of the PSF regularity witness (the `hreg`-substitution bridge).**

PSF regularity `hreg` equates the *joint* distributions of the `(image, preimage)` pairs produced
by the forward sampler `domainSample` (programmed side) and by uniform-target trapdoor sampling
(real side). The programmed random oracle answers a cache miss with `psf.eval pk (domainSample pk)`,
while the real (lazy) random oracle answers with a fresh uniform `$ᵗ Range`; off the collision, the
two tape-consuming GPV runs diverge *only* in this answer. This lemma extracts exactly the *first
marginal* of `hreg` needed to identify those two answer distributions: the programmed answer
`psf.eval pk (domainSample pk)` is distributed uniformly on `Range`.

The trapdoor-sampler suffix `s ← psf.trapdoorSample pk sk c` on the real side is discarded using its
totality (`hNF : NeverFail`), so the real first marginal collapses to the bare uniform draw
`$ᵗ Range`. This is the per-step off-collision answer agreement underlying the identical-until-bad
coupling `gpv_tvDist_tape_runs_le_collisionBound`: it is the distributional (not pointwise)
agreement of the real and programmed random-oracle answers that the identical-until-bad
machinery consumes as its no-bad-path agreement hypothesis. -/
theorem evalDist_eval_domainSample_eq_uniform (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    𝒟[(do let s ← domainSample pk; pure (psf.eval pk s) : ProbComp Range)] =
      𝒟[($ᵗ Range : ProbComp Range)] := by
  have h := congrArg (Functor.map (Prod.fst : Range × Domain → Range)) hreg
  simp only [← evalDist_map, map_bind, map_pure] at h
  rw [h]
  have hinner : ∀ a : Range,
      𝒟[(do let _ ← psf.trapdoorSample pk sk a; pure a : ProbComp Range)] =
        𝒟[(pure a : ProbComp Range)] := by
    intro a
    refine evalDist_ext fun y => ?_
    rw [probOutput_bind_const, (hNF a).probFailure_eq_zero]
    simp
  calc 𝒟[(do let a ← ($ᵗ Range); let _ ← psf.trapdoorSample pk sk a; pure a : ProbComp Range)]
      = 𝒟[(do let a ← ($ᵗ Range); pure a : ProbComp Range)] :=
        evalDist_bind_congr fun a _ => hinner a
    _ = 𝒟[($ᵗ Range : ProbComp Range)] := by simp

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off-bad agreement of the two tape handlers on a uniform query.** The uniform-query branch of
`gpvRealImplTape` and `progGameRunImplTape` are *literally identical*: both run the bare uniform
sample on the random component and leave the cache and the salt tape untouched.

This is the trivial "free query" case of the per-step no-bad-path agreement underlying the
identical-until-bad coupling `gpv_tvDist_tape_runs_le_collisionBound`: the two
tape-consuming GPV runs never diverge on a uniform query, so it contributes no charge to the bad
event. -/
theorem gpvImplTape_run_unif_eq (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (n : unifSpec.Domain) (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inl n))).run s =
      (progGameRunImplTape psf M Salt domainSample pk (.inl (.inl n))).run s := by
  rw [gpvRealImplTape_run_unif, progGameRunImplTape_run_unif]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off-bad agreement of the two tape handlers on a random-oracle read at a cached key.** On a
cache *hit* `s.1 mc = some v`, the random-oracle-read branch of `gpvRealImplTape` and
`progGameRunImplTape` are *literally identical*: the real (lazy) oracle returns the recorded value
without touching the cache, and the programmed oracle likewise returns the recorded value; both
leave the salt tape untouched.

This is the "cached read" free case of the per-step no-bad-path agreement underlying the
identical-until-bad coupling `gpv_tvDist_tape_runs_le_collisionBound`: a read that hits the
cache returns the same recorded answer on both sides (the divergence between the lazy and programmed
oracles can only arise on a *miss*, where a fresh answer is sampled). -/
theorem gpvImplTape_run_read_hit_eq (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (mc : Salt × M) (s : (Salt × M →ₒ Range).QueryCache × List Salt) (v : Range)
    (hhit : s.1 mc = some v) :
    (gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run s =
      (progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run s := by
  rw [gpvRealImplTape_run_read, progGameRunImplTape_run_read, hhit]
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1 = pure (v, s.1)
      from QueryImpl.withCaching_run_some uniformSampleImpl hhit]
  simp

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off-bad distributional agreement of the two tape handlers on a random-oracle read at a fresh
key (the `hreg`-substitution bridge, read case).** On a cache *miss* `s.1 mc = none`, the real
(lazy) random oracle answers with a fresh uniform target `$ᵗ Range`, while the programmed oracle
answers with `psf.eval pk (domainSample pk)`. By the first marginal of PSF regularity
(`evalDist_eval_domainSample_eq_uniform`) these two answer distributions coincide, and both handlers
apply the *same* deterministic post-processing of the answer (record it at `mc` in the cache and
return it, salt tape untouched). Hence the two tape handlers' read-on-miss transitions agree as
output distributions.

This is the genuinely distributional (not pointwise) per-step no-bad-path agreement underlying the
identical-until-bad coupling `gpv_tvDist_tape_runs_le_collisionBound`: it is the
read-query case
of the `hreg`-substitution bridge that the identical-until-bad machinery consumes as its
no-bad agreement hypothesis. The lazy-vs-programmed *answer* divergence is invisible to the output
distribution off the collision; it becomes observable only when the freshly recorded key later
collides with a tape salt — which is exactly the bad event `tapeCheck` charges. -/
theorem evalDist_gpvImplTape_run_read_miss_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (mc : Salt × M)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) (hmiss : s.1 mc = none)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒟[(gpvRealImplTape psf M Salt pk sk (.inl (.inr mc))).run s] =
      𝒟[(progGameRunImplTape psf M Salt domainSample pk (.inl (.inr mc))).run s] := by
  rw [gpvRealImplTape_run_read, progGameRunImplTape_run_read, hmiss]
  simp only []
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) mc).run s.1
        = (fun u => (u, s.1.cacheQuery mc u)) <$> ($ᵗ Range : ProbComp Range)
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  have hfst := evalDist_eval_domainSample_eq_uniform psf pk sk domainSample hNF hreg
  set g : Range → Range × ((Salt × M →ₒ Range).QueryCache × List Salt) :=
    fun u => (u, (s.1.cacheQuery mc u, s.2)) with hg
  have hLHS : 𝒟[((fun p : Range × (Salt × M →ₒ Range).QueryCache => (p.1, p.2, s.2)) <$>
            (fun u => (u, s.1.cacheQuery mc u)) <$> ($ᵗ Range : ProbComp Range))]
        = 𝒟[g <$> ($ᵗ Range : ProbComp Range)] := by rw [Functor.map_map]
  have hRHS : 𝒟[((fun sd => (psf.eval pk sd, s.1.cacheQuery mc (psf.eval pk sd), s.2)) <$>
            (domainSample pk : ProbComp Domain))]
        = 𝒟[g <$> (do let sd ← domainSample pk; pure (psf.eval pk sd) : ProbComp Range)] := by
    refine congrArg _ ?_
    rw [map_eq_bind_pure_comp]
    simp only [hg, map_bind, map_pure, Function.comp_def]
  exact hLHS.trans ((evalDist_map_eq_of_evalDist_eq hfst.symm g).trans hRHS.symm)

omit [DecidableEq Range] [Fintype Salt] in
open Classical in
/-- **Universal off-bad per-query agreement of the two flag-instrumented tape handlers (the
framework `h_agree_good`).** For *every* query `t` and *every* off-bad input state `(s, false)`,
the two flag handlers `gpvRealImplTapeFlag` / `progGameRunImplTapeFlag` assign equal probability to
every *off-bad output* `(u, (s', false))`.

This is the exact `h_agree_good` hypothesis of the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad`, made **universal** by the empty-tape-fires-the-flag
tweak in the flag handlers: the only state where the underlying tape handlers disagree off-flag is
the *empty-tape signing* state (where the underlying handler falls back to an inline fresh salt
draw); firing the flag there places that state inside the bad set, so on every off-bad output the
flag value is `false` exactly when the head salt is present and unkeyed — precisely the case the
per-query agreements (`gpvImplTape_run_unif_eq` for uniform, `gpvImplTape_run_read_hit_eq` /
`evalDist_gpvImplTape_run_read_miss_eq` for random-oracle reads, and
`evalDist_gpvImplTapeFlag_run_sign_offbad_eq` for unkeyed-head signing) cover. The flag bookkeeping
is `probOutput_flagTag_false`: where the flag fires the off-bad output probability is `0` on both
sides; where it stays `false` the two flagged steps reduce to their agreeing underlying steps.

It is *true-as-stated* and *pinned* to the concrete flag handlers (no free parameters); it is the
off-collision no-divergence ingredient the per-tape identical-until-bad coupling
`gpv_tvDist_tape_runs_le_collisionBound` consumes (the cardinality telescope bounds the run-level
flag probability by `collisionBound`). -/
theorem gpvImplTapeFlag_h_agree_good (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))])
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt)
    (u : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t)
    (s' : (Salt × M →ₒ Range).QueryCache × List Salt) :
    Pr[= (u, (s', false)) | (gpvRealImplTapeFlag psf M Salt pk sk t).run (s, false)]
      = Pr[= (u, (s', false)) |
          (progGameRunImplTapeFlag psf M Salt domainSample pk t).run (s, false)] := by
  cases t with
  | inl q =>
      -- Non-signing query: flag is passive (`F = false`), reduce to the underlying tape agreement.
      rw [gpvRealImplTapeFlag_run_inl, progGameRunImplTapeFlag_run_inl]
      rw [probOutput_flagTag_false, probOutput_flagTag_false, if_pos rfl, if_pos rfl]
      cases q with
      | inl n =>
          -- Uniform query: the two underlying handlers are literally identical.
          rw [gpvImplTape_run_unif_eq psf M Salt pk sk domainSample n s]
      | inr mc =>
          -- Random-oracle read: cache hit ⇒ identical; cache miss ⇒ agree by `hreg`.
          rcases h : s.1 mc with _ | v
          · exact probOutput_congr rfl
              (evalDist_gpvImplTape_run_read_miss_eq psf M Salt pk sk domainSample mc s h hNF hreg)
          · rw [gpvImplTape_run_read_hit_eq psf M Salt pk sk domainSample mc s v h]
  | inr msg =>
      -- Signing query: split on the tape.  Empty tape or keyed head ⇒ flag fires ⇒ both `0`.
      rw [gpvRealImplTapeFlag_run_inr, progGameRunImplTapeFlag_run_inr]
      rw [probOutput_flagTag_false, probOutput_flagTag_false]
      simp only [Bool.false_or]
      cases htape : s.2 with
      | nil =>
          -- Empty tape: the flag fires (`true`), both `false`-outputs have probability `0`.
          simp only [reduceCtorEq, if_false]
      | cons r tl =>
          -- Non-empty tape head `r`: split on whether it is already keyed.
          rcases hkey : saltKeyed M Salt s.1 r with _ | _
          · -- Unkeyed head: flag stays `false`; reduce to the underlying signing-miss agreement.
            simp only [hkey, if_true]
            have hmiss : s.1 (r, msg) = none := (saltKeyed_eq_false_iff M Salt s.1 r).1 hkey msg
            -- The underlying tape steps agree off-collision (joint `hreg` substitution).
            rw [show s = (s.1, r :: tl) from by rw [← htape]]
            exact probOutput_congr rfl
              (evalDist_gpvImplTape_run_sign_miss_eq psf M Salt pk sk domainSample
                msg r tl s.1 hmiss hreg)
          · -- Keyed head: the flag fires (`true`), both `false`-outputs have probability `0`.
            simp only [hkey, reduceCtorEq, if_false]

/-! ### Flag-instrumented original (inline-salt) handlers

The front-tape route front-loads every signing salt into an upfront `drawList ($ᵗ Salt) qSign`
block, which forces the cardinality telescope to *re-interleave* the upfront tape back to the
per-signing-step draws before the `saltSeq` telescope applies — a deferred-sampling fold
commutation.

The handlers below avoid that re-interleaving by flag-instrumenting the *original*
inline-salt handlers `gpvRealImpl` / `progGameRunImplNoRec`, where each signing query
draws its fresh salt `r ← $ᵗ Salt` *at* its signing step. The collision flag fires when the
inline-drawn salt `r` is already a key of the running random-oracle cache (`saltKeyed`). Because the
salt is drawn at the step (not upfront), the run-level flag probability telescopes *directly* to the
`saltSeq` form (each salt is fresh uniform against the cache slice it is checked against) — no
re-interleaving is needed. The identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` applied to these flag handlers bounds the
total-variation distance of the two original game runs by the run-level flag probability. -/

open Classical in
/-- **Flag-instrumented original real handler.** `gpvRealImpl` threaded with a collision flag: the
state is `((Salt × M →ₒ Range).QueryCache × Bool)`. Uniform and random-oracle-read queries leave the
flag untouched; a signing query draws its fresh inline salt `r ← $ᵗ Salt`, sets the flag if `r` is
already a key of the cache (`saltKeyed`), monotonically OR-ing into the prior flag, then runs the
underlying `gpvRealImpl` signing body on it. Its `run'`-projection (dropping the flag) is the
original `gpvRealImpl`.

Unlike the tape handler `gpvRealImplTapeFlag`, the salt is drawn *inline at the signing step*, so
the collision decision is made against the cache the body actually queries, and there is no
empty-tape fallback branch: the off-bad per-query agreement is genuinely universal (no spurious bad
state). -/
noncomputable def gpvRealImplFlag (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$> (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), (p.2, s.2 || saltKeyed M Salt s.1 r))

open Classical in
/-- **Flag-instrumented original programmed handler.** The programmed dual of `gpvRealImplFlag`:
`progGameRunImplNoRec` threaded with the same collision flag (set on a signing step when the
inline-drawn salt `r` is already a key of the cache). Its `run'`-projection is the original
`progGameRunImplNoRec`. -/
noncomputable def progGameRunImplNoRecFlag (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$>
          (progGameRunImplNoRec psf M Salt domainSample pk (.inl q)).run s.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sgn ← (domainSample pk : ProbComp Domain)
        pure ((r, sgn), (s.1.cacheQuery (r, msg) (psf.eval pk sgn), s.2 || saltKeyed M Salt s.1 r))

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFlag` on a non-signing query.** The flag is untouched; the
underlying `gpvRealImpl` runs on the cache component. -/
lemma gpvRealImplFlag_run_inl (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    (gpvRealImplFlag psf hr M Salt pk sk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$> (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1 := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRecFlag` on a non-signing query.** -/
lemma progGameRunImplNoRecFlag_run_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    (progGameRunImplNoRecFlag psf M Salt domainSample pk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl q)).run s.1 := rfl

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFlag` on a signing query.** The fresh inline salt `r` is
drawn, the real signing body runs the lazy random oracle at `(r, msg)` and trapdoor-samples, and the
flag is OR-ed with the collision predicate `saltKeyed` on the inline salt. -/
lemma gpvRealImplFlag_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    (gpvRealImplFlag psf hr M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), (p.2, s.2 || saltKeyed M Salt s.1 r))) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRecFlag` on a signing query.** -/
lemma progGameRunImplNoRecFlag_run_inr (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    (progGameRunImplNoRecFlag psf M Salt domainSample pk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sgn ← (domainSample pk : ProbComp Domain)
        pure ((r, sgn),
          (s.1.cacheQuery (r, msg) (psf.eval pk sgn), s.2 || saltKeyed M Salt s.1 r))) := rfl

omit [Fintype Salt] in
/-- **Per-query flag-projection of the real flag handler.** Dropping the flag component
(`Prod.map id Prod.fst`) from one `gpvRealImplFlag` query step recovers the corresponding
`gpvRealImpl` step on the flagless cache state. The flag is a passive auxiliary: it is written by
the signing step but never affects the output or the cache, so projecting it away yields the
original handler. This is the per-query hypothesis of the state-projection transport
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma gpvRealImplFlag_proj_fst (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    Prod.map id (Prod.fst : (Salt × M →ₒ Range).QueryCache × Bool →
        (Salt × M →ₒ Range).QueryCache) <$>
        (gpvRealImplFlag psf hr M Salt pk sk t).run s =
      (gpvRealImpl psf hr M Salt pk sk t).run s.1 := by
  cases t with
  | inl q => rw [gpvRealImplFlag_run_inl]; simp [Functor.map_map, Prod.map]
  | inr msg =>
      rw [gpvRealImplFlag_run_inr, gpvRealImpl_run_sign]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-query flag-projection of the programmed flag handler.** The programmed dual of
`gpvRealImplFlag_proj_fst`: dropping the flag recovers `progGameRunImplNoRec`. -/
lemma progGameRunImplNoRecFlag_proj_fst (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    Prod.map id (Prod.fst : (Salt × M →ₒ Range).QueryCache × Bool →
        (Salt × M →ₒ Range).QueryCache) <$>
        (progGameRunImplNoRecFlag psf M Salt domainSample pk t).run s =
      (progGameRunImplNoRec psf M Salt domainSample pk t).run s.1 := by
  cases t with
  | inl q => rw [progGameRunImplNoRecFlag_run_inl]; simp [Functor.map_map, Prod.map]
  | inr msg =>
      rw [progGameRunImplNoRecFlag_run_inr, progGameRunImplNoRec_run_sign]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [Fintype Salt] in
/-- **Run-level flag-projection of the real flag handler.** Dropping the flag from the full
simulated run of `gpvRealImplFlag` over `adv.main pk` recovers the flagless run of `gpvRealImpl`.
This transports the per-query projection `gpvRealImplFlag_proj_fst` through the whole adversary via
`map_run_simulateQ_eq_of_query_map_eq`, witnessing that the collision flag is a passive instrument:
its addition does not change the output-and-cache distribution. -/
lemma map_run_gpvRealImplFlag_eq (pk : PK) (sk : SK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (M × (Salt × Domain)))
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    Prod.map id (Prod.fst : (Salt × M →ₒ Range).QueryCache × Bool →
        (Salt × M →ₒ Range).QueryCache) <$>
        (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run s =
      (simulateQ (gpvRealImpl psf hr M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (gpvRealImplFlag_proj_fst psf hr M Salt pk sk) oa s

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Run-level flag-projection of the programmed flag handler.** The programmed dual of
`map_run_gpvRealImplFlag_eq`. -/
lemma map_run_progGameRunImplNoRecFlag_eq (domainSample : PK → ProbComp Domain) (pk : PK)
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (M × (Salt × Domain)))
    (s : (Salt × M →ₒ Range).QueryCache × Bool) :
    Prod.map id (Prod.fst : (Salt × M →ₒ Range).QueryCache × Bool →
        (Salt × M →ₒ Range).QueryCache) <$>
        (simulateQ (progGameRunImplNoRecFlag psf M Salt domainSample pk) oa).run s =
      (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (progGameRunImplNoRecFlag_proj_fst psf M Salt domainSample pk) oa s

omit [Fintype Salt] in
/-- **Bad-monotonicity of the real flag handler.** Once the collision flag is set on the input state
(`p.2 = true`), every output of one `gpvRealImplFlag` query step also carries the flag set: the
non-signing branch preserves `s.2`, and the signing branch only OR-s a new collision indicator into
it. This is the `h_mono` hypothesis the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` consumes: the bad event is absorbing. -/
lemma gpvRealImplFlag_bad_mono (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : (Salt × M →ₒ Range).QueryCache × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((gpvRealImplFlag psf hr M Salt pk sk t).run p), z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [gpvRealImplFlag_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      rw [gpvRealImplFlag_run_inr] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨r, _, c, _, sgn, _, hw⟩ := hz
      subst hw; simp [hp]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Bad-monotonicity of the programmed flag handler.** The programmed dual of
`gpvRealImplFlag_bad_mono`. -/
lemma progGameRunImplNoRecFlag_bad_mono (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : (Salt × M →ₒ Range).QueryCache × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((progGameRunImplNoRecFlag psf M Salt domainSample pk t).run p),
      z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [progGameRunImplNoRecFlag_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      rw [progGameRunImplNoRecFlag_run_inr] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨r, _, sgn, _, hw⟩ := hz
      subst hw; simp [hp]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Salt] in
/-- **Off-bad joint agreement of the two original-run flag signing steps on a fresh inline salt (the
`hreg` substitution bridge, inline-salt signing case).** With the inline salt `r` *fixed* and *not
yet keyed* in the cache (`cache (r, msg) = none`, so the collision flag stays `false`), the full
signing-step body output distributions of `gpvRealImplFlag` and `progGameRunImplNoRecFlag` — the
returned signature `(r, sgn)`, the updated cache, and the (still `false`) flag — *coincide*.

The real side runs the lazy random oracle at `(r, msg)` (a miss, so it draws a fresh uniform target
`c ← $ᵗ Range`, records `(r, msg) ↦ c`), draws a trapdoor preimage `sgn ← trapdoorSample pk sk c`,
and tags the flag `false`; the programmed side forward-samples `sgn ← domainSample pk`, records
`(r, msg) ↦ psf.eval pk sgn`, and tags the flag `false`. Both apply the *same* deterministic
post-processing `fun (c, s) => ((r, s), cache.cacheQuery (r, msg) c, false)` to a `(target,
preimage)` pair drawn from two distributions that coincide by PSF regularity `hreg`. This is the
inline-salt analogue of `evalDist_gpvImplTape_run_sign_miss_eq`, the signing-query case of the
universal off-bad agreement `gpvImplFlag_h_agree_good`. It is *pinned* to the concrete flag handlers
(no free parameters). -/
theorem evalDist_gpvImplFlag_run_sign_offbad_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (msg : M) (r : Salt)
    (cache : (Salt × M →ₒ Range).QueryCache) (hmiss : cache (r, msg) = none)
    (hreg : 𝒟[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒟[(do
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        let sgn ← psf.trapdoorSample pk sk p.1
        pure (((r, sgn), (p.2, false)) :
          (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))]
      = 𝒟[(do
          let sgn ← (domainSample pk : ProbComp Domain)
          pure (((r, sgn), (cache.cacheQuery (r, msg) (psf.eval pk sgn), false)) :
            (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))] := by
  classical
  set g : Range × Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool) :=
    fun cs => ((r, cs.2), (cache.cacheQuery (r, msg) cs.1, false)) with hg
  rw [show (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        = (fun u => (u, cache.cacheQuery (r, msg) u)) <$> ($ᵗ Range : ProbComp Range)
      from QueryImpl.withCaching_run_none uniformSampleImpl hmiss]
  have hLHS :
      𝒟[(do
          let p ← (fun u => (u, cache.cacheQuery (r, msg) u)) <$> ($ᵗ Range : ProbComp Range)
          let sgn ← psf.trapdoorSample pk sk p.1
          pure (((r, sgn), (p.2, false)) :
            (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))]
        = 𝒟[g <$> (do let c ← ($ᵗ Range); let sgn ← psf.trapdoorSample pk sk c; pure (c, sgn)
              : ProbComp (Range × Domain))] := by
    simp only [hg, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  have hRHS :
      𝒟[(do
          let sgn ← (domainSample pk : ProbComp Domain)
          pure (((r, sgn), (cache.cacheQuery (r, msg) (psf.eval pk sgn), false)) :
            (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))]
        = 𝒟[g <$> (do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
              : ProbComp (Range × Domain))] := by
    simp only [hg, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine hLHS.trans (Eq.trans ?_ hRHS.symm)
  exact evalDist_map_eq_of_evalDist_eq hreg.symm g

omit [Fintype Salt] in
open Classical in
/-- **Off-bad random-oracle-read agreement of the two original handlers.** On a random-oracle read
the underlying `gpvRealImpl` and `progGameRunImplNoRec` agree in distribution: on a cache hit both
return the recorded value with the cache unchanged; on a cache miss the real lazy oracle draws a
fresh uniform answer while the programmed oracle answers `psf.eval pk (domainSample pk)` and records
it, and these two answers are equally distributed by the first marginal of `hreg`. This is the
random-oracle-read case of the universal off-bad agreement `gpvImplFlag_h_agree_good`. -/
theorem evalDist_gpvImpl_run_read_eq (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (mc : Salt × M) (cache : (Salt × M →ₒ Range).QueryCache)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒟[(gpvRealImpl psf hr M Salt pk sk (.inl (.inr mc))).run cache]
      = 𝒟[(progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr mc))).run cache] := by
  classical
  rw [gpvRealImpl_run_read, progGameRunImplNoRec_run_read]
  rcases h : cache mc with _ | v
  · -- Cache miss: real draws a fresh uniform answer; prog programs `eval ∘ domainSample`.
    rw [QueryImpl.withCaching_run_none uniformSampleImpl h]
    simp only []
    -- The first marginal of `hreg`: `eval ∘ domainSample ~ $ᵗ Range`.
    have hfst := evalDist_eval_domainSample_eq_uniform psf pk sk domainSample hNF hreg
    -- Both sides are `g <$> (·)` for `g w = (w, cache.cacheQuery mc w)` on the equal answers.
    calc 𝒟[(fun u => (u, cache.cacheQuery mc u)) <$>
            (uniformSampleImpl (spec := (Salt × M →ₒ Range)) mc)]
        = 𝒟[(fun w : Range => (w, cache.cacheQuery mc w)) <$> ($ᵗ Range : ProbComp Range)] := rfl
      _ = 𝒟[(fun w : Range => (w, cache.cacheQuery mc w)) <$>
            (do let sd ← domainSample pk; pure (psf.eval pk sd) : ProbComp Range)] :=
          evalDist_map_eq_of_evalDist_eq hfst.symm _
      _ = 𝒟[(fun sd : Domain => (psf.eval pk sd, cache.cacheQuery mc (psf.eval pk sd))) <$>
            (domainSample pk : ProbComp Domain)] := by
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · -- Cache hit: both return the recorded value, cache unchanged.
    rw [QueryImpl.withCaching_run_some uniformSampleImpl h]
    rfl

omit [Fintype Salt] in
open Classical in
/-- **Universal off-bad per-query agreement of the two original-run flag handlers (the framework
`h_agree_good`).** For *every* query `t` and *every* off-bad input state `(s, false)`, the two flag
handlers `gpvRealImplFlag` / `progGameRunImplNoRecFlag` assign equal probability to every *off-bad
output* `(u, (s', false))`.

This is the exact `h_agree_good` hypothesis of the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad`. It is genuinely *universal* without any spurious
"empty-tape" bad state: the salt of each signing query is drawn *inline at the step*, so on a
signing query the off-bad output probability splits (over the inline salt `r`) into a sum whose
keyed-`r` summands vanish (the flag fires, so the `false`-flag output has probability `0` on both
sides) and whose unkeyed-`r` summands agree by the inline-salt signing-miss bridge
`evalDist_gpvImplFlag_run_sign_offbad_eq`. Non-signing queries reduce to the underlying
`gpvRealImpl` / `progGameRunImplNoRec` agreement (uniform: literally identical; random-oracle read:
cache hit identical, cache miss distributional by `hreg`).

It is *true-as-stated* and *pinned* to the concrete flag handlers (no free parameters). -/
theorem gpvImplFlag_h_agree_good (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))])
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache)
    (u : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t)
    (s' : (Salt × M →ₒ Range).QueryCache) :
    Pr[= (u, (s', false)) | (gpvRealImplFlag psf hr M Salt pk sk t).run (s, false)]
      = Pr[= (u, (s', false)) |
          (progGameRunImplNoRecFlag psf M Salt domainSample pk t).run (s, false)] := by
  cases t with
  | inl q =>
      -- Non-signing query: flag is passive (`F = false`), reduce to the underlying agreement.
      rw [gpvRealImplFlag_run_inl, progGameRunImplNoRecFlag_run_inl]
      rw [probOutput_flagTag_false, probOutput_flagTag_false, if_pos rfl, if_pos rfl]
      cases q with
      | inl n =>
          -- Uniform query: the two underlying handlers are literally identical.
          rw [gpvRealImpl_run_unif, progGameRunImplNoRec_run_unif]
      | inr mc =>
          -- Random-oracle read: agree by the underlying read agreement (hit/miss by `hreg`).
          exact probOutput_congr rfl
            (evalDist_gpvImpl_run_read_eq psf hr M Salt pk sk domainSample mc s hNF hreg)
  | inr msg =>
      -- Signing query: split over the inline salt `r`.  Keyed `r` ⇒ flag fires ⇒ both `0`;
      -- unkeyed `r` ⇒ flag stays `false` ⇒ bodies agree by the inline-salt signing-miss bridge.
      rw [gpvRealImplFlag_run_inr, progGameRunImplNoRecFlag_run_inr]
      simp only [Bool.false_or]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine tsum_congr (fun r => ?_)
      refine congrArg _ ?_
      rcases hkey : saltKeyed M Salt s r with _ | _
      · -- Unkeyed salt `r`: flag stays `false`; bodies agree.
        have hmiss : s (r, msg) = none := (saltKeyed_eq_false_iff M Salt s r).1 hkey msg
        exact probOutput_congr rfl
          (evalDist_gpvImplFlag_run_sign_offbad_eq psf M Salt pk sk domainSample
            msg r s hmiss hreg)
      · -- Keyed salt `r`: the flag fires (`true`); the `false`-flag output has probability `0`.
        rw [probOutput_eq_zero_of_not_mem_support, probOutput_eq_zero_of_not_mem_support]
        · -- Real side support: every output carries flag `true`.
          intro hmem
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          tauto
        · -- Programmed side support: every output carries flag `true`.
          intro hmem
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          tauto

omit [Fintype Salt] in
open Classical in
/-- **Original-run framework reduction of Step 1 to the run-level collision flag.** The
total-variation distance between the two *original* GPV game runs `realGameRun` / `progGameRun` is
bounded by the run-level collision-flag probability of the flag-instrumented real run
`gpvRealImplFlag`.

This is the direct application of the framework identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` to the flag-instrumented original handlers
`gpvRealImplFlag` / `progGameRunImplNoRecFlag`, fed the universal off-bad per-query agreement
`gpvImplFlag_h_agree_good` and the bad-monotonicity `gpvRealImplFlag_bad_mono` /
`progGameRunImplNoRecFlag_bad_mono` (the `h_mono` hypotheses).  The run-level flag projection
`map_run_gpvRealImplFlag_eq` / `map_run_progGameRunImplNoRecFlag_eq` identifies the output
projection of the flagless original run with that of the flagged run, and
`realGameRun_eq_run'_implReal` / `progGameRun_eq_run'_implNoRec` pin those flagless output
projections to the actual game runs; the data-processing contraction `tvDist_map_le` then reduces
the framework total-variation bound to the original-run TV distance.

Unlike the front-tape reduction `gpv_tvDist_tape_run_le_probEvent_flag`, there is **no upfront salt
tape**: each signing salt is drawn inline at its step, so the run-level flag probability telescopes
*directly* to the salt-averaged birthday term (no re-interleaving). -/
theorem gpv_tvDist_orig_run_le_probEvent_flag (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    SPMF.tvDist (realGameRun psf hr M Salt adv pk sk)
        (progGameRun psf hr M Salt adv domainSample pk)
      ≤ Pr[fun z : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), false)].toReal := by
  -- Pin both game runs to the output projections of the flagless original runs.
  rw [realGameRun_eq_run'_implReal, progGameRun_eq_run'_implNoRec, StateT.run', StateT.run']
  -- Move to the `OracleComp.tvDist` form (`SPMF.tvDist 𝒟[·] 𝒟[·] = tvDist · ·`).
  change tvDist (Prod.fst <$> (simulateQ (gpvRealImpl psf hr M Salt pk sk) (adv.main pk)).run
        (∅ : (Salt × M →ₒ Range).QueryCache))
      (Prod.fst <$> (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (adv.main pk)).run
        (∅ : (Salt × M →ₒ Range).QueryCache)) ≤ _
  -- The output projection of each flagless run equals the doubly-projected flagged run.
  have hreal := map_run_gpvRealImplFlag_eq psf hr M Salt pk sk (adv.main pk)
    ((∅ : (Salt × M →ₒ Range).QueryCache), false)
  have hprog := map_run_progGameRunImplNoRecFlag_eq psf M Salt domainSample pk (adv.main pk)
    ((∅ : (Salt × M →ₒ Range).QueryCache), false)
  rw [show (Prod.fst <$> (simulateQ (gpvRealImpl psf hr M Salt pk sk) (adv.main pk)).run
          (∅ : (Salt × M →ₒ Range).QueryCache))
        = (fun z : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × Bool) => z.1) <$>
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), false) from by
      rw [← hreal, Functor.map_map]; rfl]
  rw [show (Prod.fst <$> (simulateQ (progGameRunImplNoRec psf M Salt domainSample pk)
          (adv.main pk)).run (∅ : (Salt × M →ₒ Range).QueryCache))
        = (fun z : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × Bool) => z.1) <$>
          (simulateQ (progGameRunImplNoRecFlag psf M Salt domainSample pk) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), false) from by
      rw [← hprog, Functor.map_map]; rfl]
  -- Data-processing contraction then the framework identical-until-bad bound.
  refine le_trans (tvDist_map_le _ _ _) ?_
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    (gpvRealImplFlag psf hr M Salt pk sk) (progGameRunImplNoRecFlag psf M Salt domainSample pk)
    (adv.main pk) (∅ : (Salt × M →ₒ Range).QueryCache)
    (gpvImplFlag_h_agree_good psf hr M Salt pk sk domainSample hNF hreg)
    (gpvRealImplFlag_bad_mono psf hr M Salt pk sk)
    (progGameRunImplNoRecFlag_bad_mono psf M Salt domainSample pk)

/-- **Finset of salts already keyed in the random-oracle cache.** The salts `r` for which some
random-oracle key `(r, m)` is already recorded (`saltKeyed`).  Its cardinality is the size of the
cache slice the inline signing salt is charged against in the `(A2)` telescope: a fresh uniform salt
lands in it with probability `card / |Salt|` (`probEvent_mem_uniformSample`). -/
noncomputable def keyedSalts (cache : (Salt × M →ₒ Range).QueryCache) : Finset Salt :=
  Finset.univ.filter (fun r : Salt => saltKeyed M Salt cache r)

omit [DecidableEq Range] [SampleableType Range] [SampleableType Salt] in
/-- **Cache-slice growth on one recorded random-oracle answer.** Recording a single random-oracle
entry `(r, msg) ↦ v` enlarges the keyed-salt slice by at most one element (the salt `r`): every
other salt's keyed status is unchanged, since `cacheQuery` only updates the key `(r, msg)`.  This is
the per-step cache-growth bound that drives the `(A2)` cardinality telescope (`card (cache j) ≤
j + qHash`). -/
lemma keyedSalts_cacheQuery_card_le (cache : (Salt × M →ₒ Range).QueryCache)
    (r : Salt) (msg : M) (v : Range) :
    (keyedSalts M Salt (cache.cacheQuery (r, msg) v)).card
      ≤ (keyedSalts M Salt cache).card + 1 := by
  classical
  refine le_trans (Finset.card_le_card ?_) (le_trans (Finset.card_insert_le r
    (keyedSalts M Salt cache)) (by rw [add_comm]))
  intro s hs
  simp only [keyedSalts, Finset.mem_filter, Finset.mem_univ, true_and, saltKeyed,
    decide_eq_true_eq] at hs
  obtain ⟨m, hm⟩ := hs
  simp only [Finset.mem_insert, keyedSalts, Finset.mem_filter, Finset.mem_univ, true_and,
    saltKeyed, decide_eq_true_eq]
  by_cases hsr : s = r
  · exact Or.inl hsr
  · refine Or.inr ⟨m, ?_⟩
    have hne : (s, m) ≠ (r, msg) := by
      simp only [ne_eq, Prod.mk.injEq, not_and]; intro h; exact absurd h hsr
    rwa [OracleSpec.QueryCache.cacheQuery_of_ne (cache := cache) (u := v) hne] at hm

omit [DecidableEq Range] [SampleableType Salt] in
/-- **Cache-slice growth through one lazy random-oracle read.** Any state `p` reachable from a
single lazy random-oracle step `(randomOracle mc).run cache` enlarges the keyed-salt slice by at
most one element: on a cache hit the cache is unchanged, and on a miss the new entry is recorded via
`cacheQuery`, which adds at most one keyed salt (`keyedSalts_cacheQuery_card_le`). -/
lemma keyedSalts_randomOracle_run_card_le (mc : Salt × M)
    (cache : (Salt × M →ₒ Range).QueryCache)
    (p : Range × (Salt × M →ₒ Range).QueryCache)
    (hp : p ∈ support ((randomOracle (spec := (Salt × M →ₒ Range)) mc).run cache)) :
    (keyedSalts M Salt p.2).card ≤ (keyedSalts M Salt cache).card + 1 := by
  classical
  rcases hcache : cache mc with _ | u
  · rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache] at hp
    rw [support_map] at hp
    obtain ⟨v, -, rfl⟩ := hp
    exact keyedSalts_cacheQuery_card_le M Salt cache mc.1 mc.2 v
  · rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache] at hp
    rw [support_pure] at hp
    obtain rfl := hp
    exact Nat.le_succ _

open Classical in
/-- **(A2) cardinality-telescope auxiliary (general motive).**

The general-motive inductive core behind `gpv_orig_flag_le_collisionBound`: over an arbitrary
adversary computation `oa`, the run-level collision-flag probability of `gpvRealImplFlag` started
from a state `(cache, false)` is bounded by the running birthday sum `∑_{j < qS} (m + j) / |Salt|`,
provided `oa` makes at most `qS` signing and `qH` hash queries and the keyed-salt slice of the
starting cache satisfies `card (keyedSalts cache) + qH ≤ m`.

Proved by `OracleComp.inductionOn` over `oa`, generalizing the cache, the residual signing/hash
budgets, and the offset `m`.  At a signing step the fresh inline salt `r ← $ᵗ Salt` is drawn
*independently* of the running cache, so it lands in `keyedSalts cache` with probability
`card (keyedSalts cache) / |Salt| ≤ m / |Salt|` (`probEvent_mem_uniformSample`); on the
non-collision branch the cache slice grows by at most one (`keyedSalts_cacheQuery_card_le`), so the
continuation is bounded by the IH at offset `m + 1` and residual budget `qS - 1`, and the per-step
union recombines to the running sum.  Non-signing steps leave the flag untouched; a uniform step
leaves the cache unchanged and a read step grows the slice by at most one (absorbed by `qH`). -/
theorem gpv_orig_flag_le_collisionBound_aux [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (cache : (Salt × M →ₒ Range).QueryCache) (m qS qH : ℕ),
      oa.IsQueryBoundP (· matches .inr _) qS →
      oa.IsQueryBoundP (· matches .inl (.inr _)) qH →
      (keyedSalts M Salt cache).card + qH ≤ m →
      Pr[fun z : β × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, false)]
        ≤ ∑ j ∈ Finset.range qS, ((m + j : ℕ) : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro cache m qS qH _ _ _
      simp [simulateQ_pure, StateT.run_pure]
  | query_bind t mx ih =>
      intro cache m qS qH hQS hQH hcard
      rw [simulateQ_query_bind, StateT.run_bind]
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQS hQH
      obtain ⟨hQS1, hQS2⟩ := hQS
      obtain ⟨hQH1, hQH2⟩ := hQH
      rcases t with (n | mc) | msg
      · -- uniform query: flag and cache untouched
        simp only [OracleQuery.input_query, monadLift_self,
          gpvRealImplFlag_run_inl, gpvRealImpl_run_unif, map_eq_bind_pure_comp, bind_assoc,
          Function.comp_apply, pure_bind]
        refine probEvent_bind_le_of_forall_le (fun x hx => ?_)
        obtain ⟨u, -, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
        simp only [Function.comp_apply] at hx
        subst hx
        have hbS := hQS2 u
        have hbH := hQH2 u
        simp only [Bool.false_eq_true, if_false] at hbS hbH
        exact ih u cache m qS qH hbS hbH hcard
      · -- random-oracle read: flag untouched, cache slice grows ≤ 1
        have hqH : 0 < qH := by
          simpa using hQH1
        simp only [OracleQuery.input_query, monadLift_self,
          gpvRealImplFlag_run_inl, gpvRealImpl_run_read]
        rw [map_eq_bind_pure_comp, bind_assoc]
        refine probEvent_bind_le_of_forall_le (fun p hp => ?_)
        simp only [Function.comp_apply, pure_bind]
        have hbS := hQS2 p.1
        have hbH := hQH2 p.1
        simp only [Bool.false_eq_true, if_false, if_true] at hbS hbH
        have hcard' : (keyedSalts M Salt p.2).card + (qH - 1) ≤ m := by
          have hgrow := keyedSalts_randomOracle_run_card_le M Salt mc cache p hp
          omega
        exact ih p.1 p.2 m qS (qH - 1) hbS hbH hcard'
      · -- signing query: the inline salt is charged against the keyed-salt slice
        have hqS : 0 < qS := by simpa using hQS1
        simp only [OracleQuery.input_query, monadLift_self, gpvRealImplFlag_run_inr]
        -- Reassociate the inline salt draw to the front of the whole step + continuation.
        rw [bind_assoc]
        -- Split the running sum into the head charge `(m)/|Salt|` and the IH tail.
        rw [show qS = (qS - 1) + 1 from (Nat.succ_pred_eq_of_pos hqS).symm,
          Finset.sum_range_succ', add_comm]
        -- Phrase the collision event in the `¬ · = false` form expected by `probEvent_bind_le_add`.
        refine le_trans (le_of_eq (probEvent_congr'
          (q := fun z => ¬ z.2.2 = false) (oa' := _)
          (fun z _ => by cases h : z.2.2 <;> simp [h]) rfl)) ?_
        -- Head charge: the fresh inline salt lands in `keyedSalts cache` w.p. `≤ m / |Salt|`.
        have hhead :
            Pr[fun r : Salt => ¬ (fun r : Salt => saltKeyed M Salt cache r = false) r |
                ($ᵗ Salt : ProbComp Salt)]
              ≤ ((m + 0 : ℕ) : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) := by
          have hkey : (fun r : Salt => ¬ saltKeyed M Salt cache r = false)
              = (fun r : Salt => r ∈ keyedSalts M Salt cache) := by
            funext r
            simp only [keyedSalts, Finset.mem_filter, Finset.mem_univ, true_and,
              Bool.not_eq_false]
          rw [show (fun r : Salt => saltKeyed M Salt cache r = false → False)
              = (fun r : Salt => r ∈ keyedSalts M Salt cache) from hkey,
            probEvent_mem_uniformSample]
          gcongr
          exact_mod_cast hcard.trans' (Nat.le_add_right _ _)
        -- Off-collision tail: the continuation is bounded by the IH at offset `m + 1`.
        have htail : ∀ r ∈ support ($ᵗ Salt : ProbComp Salt),
            (fun r : Salt => saltKeyed M Salt cache r = false) r →
            Pr[fun z : β × ((Salt × M →ₒ Range).QueryCache × Bool) =>
                ¬ z.2.2 = false |
              (do
                let p ← (randomOracle (r, msg)).run cache
                let sgn ← psf.trapdoorSample pk sk p.1
                pure ((r, sgn), p.2, false || saltKeyed M Salt cache r)) >>=
              fun p_1 => (simulateQ (gpvRealImplFlag psf hr M Salt pk sk)
                (mx ((OracleSpec.query (Sum.inr msg)).cont p_1.1))).run p_1.2]
              ≤ ∑ j ∈ Finset.range (qS - 1),
                ((m + (j + 1) : ℕ) : ℝ≥0∞) / (Fintype.card Salt : ℝ≥0∞) := by
          intro r _ hr
          -- Convert the event back to `z.2.2 = true` (cleaner for the IH).
          refine le_trans (le_of_eq (probEvent_congr' (q := fun z => z.2.2 = true) (oa' := _)
            (fun z _ => by cases h : z.2.2 <;> simp [h]) rfl)) ?_
          -- Bound the continuation pointwise over the signing-step outputs.
          rw [bind_assoc]
          refine probEvent_bind_le_of_forall_le (fun p hp => ?_)
          rw [bind_assoc]
          refine probEvent_bind_le_of_forall_le (fun sgn _ => ?_)
          rw [pure_bind]
          -- On the off-collision branch the flag stays false; the cache `p.2` grew by ≤ 1.
          simp only [hr, Bool.or_false]
          have hbS := hQS2 (r, sgn)
          have hbH := hQH2 (r, sgn)
          simp only [if_true, Bool.false_eq_true, if_false] at hbS hbH
          refine le_trans (ih (r, sgn) p.2 (m + 1) (qS - 1) qH hbS hbH ?_)
            (le_of_eq (Finset.sum_congr rfl fun j _ => by
              rw [show m + 1 + j = m + (j + 1) from by omega]))
          -- Cache-growth invariant: `card (keyedSalts p.2) + qH ≤ m + 1`.
          have hgrow := keyedSalts_randomOracle_run_card_le M Salt (r, msg) cache p hp
          omega
        exact probEvent_bind_le_add hhead htail

open Classical in
/-- **(A2) Original-run cardinality telescope: the run-level collision flag of the inline-salt real
handler is bounded by `collisionBound`.**

The run-level collision-flag probability of the flag-instrumented *original* real run of
`adv.main pk` (started from the empty cache and an unset flag) is bounded by
`(collisionBound Salt qSign qHash).toReal`.

The flag fires when an inline-drawn signing salt `r ← $ᵗ Salt` lands on a key already recorded in
the running random-oracle cache.  Because the salt is drawn *at* its signing step (not pre-drawn
into an upfront tape), an `OracleComp.inductionOn` over `adv.main pk` threads the partial flag
probability `Pr[flag fired in the first j queries]` across the adaptive adversary; at the `j`-th
signing step the inline salt `r` is a fresh uniform `$ᵗ Salt` *independent of the running cache*
(it has not yet been
revealed at that point), so it lands on the cache slice with probability `card (cache j) / |Salt|`
(`probEvent_mem_uniformSample`), where `card (cache j) ≤ j + qHash` by the cache-growth invariant
(`hQ` bounds the adversary to `≤ qSign` signing salts and `≤ qHash` hash-query cache entries).
Summing
`∑_{j < qSign} (j + qHash) / |Salt| = (qSign + qHash)² / (2 |Salt|) = collisionBound`
(`sum_range_div_card_le_collisionBound`) gives the bound, mapping onto the
`probEvent_saltSeq_le_collisionBound` telescope — *without* the front-tape re-interleaving the
upfront-tape route required.

It is *true-as-stated* (counterexample-checked at `qSign = 0`: `hQ` permits no signing query, so the
flag — which only fires on a signing step — is never set, the flag probability is `0`, and
`0 ≤ (collisionBound …).toReal`) and *pinned* to the concrete flag handler `gpvRealImplFlag` and the
actual game-run vehicle `adv.main pk` (NOT free parameters).  It carries the run-level coupling
content; the off-collision per-query agreement it pairs with is `gpvImplFlag_h_agree_good`
(universal), and the reduction of Step 1's TV to this flag probability is
`gpv_tvDist_orig_run_le_probEvent_flag`. -/
theorem gpv_orig_flag_le_collisionBound [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun z : (M × (Salt × Domain)) × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
        (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), false)].toReal
      ≤ (collisionBound Salt qSign qHash).toReal := by
  -- Instantiate the general-motive auxiliary at the empty cache, with `m := qHash`, charging each
  -- fresh inline signing salt against the running cache slice; then finish with the Gauss-sum
  -- estimate `sum_range_div_card_le_collisionBound`.
  obtain ⟨hQS, hQH⟩ := hQ
  have hempty : (keyedSalts M Salt (∅ : (Salt × M →ₒ Range).QueryCache)).card = 0 := by
    rw [Finset.card_eq_zero]
    refine Finset.filter_eq_empty_iff.2 (fun r _ => ?_)
    simp [saltKeyed]
  have haux := gpv_orig_flag_le_collisionBound_aux psf hr M Salt pk sk (adv.main pk)
    (∅ : (Salt × M →ₒ Range).QueryCache) qHash qSign qHash hQS hQH (by omega)
  have hbound : (probEvent ((simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk)).run
      ((∅ : (Salt × M →ₒ Range).QueryCache), false)) fun z => z.2.2 = true)
      ≤ collisionBound Salt qSign qHash := by
    refine haux.trans (le_trans (Finset.sum_le_sum fun j _ => ?_)
      (sum_range_div_card_le_collisionBound Salt qSign qHash))
    rw [Nat.add_comm qHash j]
  refine ENNReal.toReal_mono ?_ hbound
  unfold collisionBound
  exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])

omit [Fintype Salt] in
/-- **Flag-neutrality of a signing-free continuation (real flag handler).**
The collision flag of `gpvRealImplFlag` is set *only* on a signing step. Hence a computation `ob`
that issues **no** signing query (`ob.IsQueryBoundP (· matches .inr _) 0`) cannot move the flag: run
from `(cache, b)`, every output state still carries flag `b`.

Proved by `OracleComp.inductionOn` over `ob`: the `pure` case is immediate; a `.inl` (uniform /
random-oracle) step leaves the flag at `s.2 = b` (`gpvRealImplFlag_run_inl`) and the IH applies; a
`.inr` (signing) step is excluded because the query bound forbids it (`0 < 0` is false).

This is the key fact that keeps the verify-Bool lift on the *same* `collisionBound`: appending the
verification read (a signing-free `.inl` continuation) after `adv.main pk` adds no flag mass, so no
extra `qHash` budget is charged. -/
theorem gpvRealImplFlag_run_no_sign_flag_eq [Inhabited Range] (pk : PK) (sk : SK) :
    ∀ {γ : Type}
      (ob : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
      (cache : (Salt × M →ₒ Range).QueryCache) (b : Bool),
      ob.IsQueryBoundP (· matches .inr _) 0 →
      ∀ z ∈ support ((simulateQ (gpvRealImplFlag psf hr M Salt pk sk) ob).run (cache, b)),
        z.2.2 = b := by
  intro γ ob
  induction ob using OracleComp.inductionOn with
  | pure x =>
      intro cache b _ z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; rfl
  | query_bind t mx ih =>
      intro cache b hQ z hz
      rw [simulateQ_query_bind, StateT.run_bind] at hz
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ0, hQrec⟩ := hQ
      simp only [mem_support_bind_iff] at hz
      obtain ⟨w, hw, hz⟩ := hz
      rcases t with q | msg
      · -- non-signing step: the flag stays `s.2 = b`, then apply the IH.
        simp only [OracleQuery.input_query, monadLift_self, gpvRealImplFlag_run_inl] at hw
        simp only [support_map] at hw
        obtain ⟨v, _, hv⟩ := hw
        have hwb : w.2.2 = b := by rw [← hv]
        have hbS := hQrec w.1
        simp only [Bool.false_eq_true, if_false] at hbS
        have := ih w.1 w.2.1 w.2.2 hbS z hz
        rw [this, hwb]
      · -- signing step is excluded: `0 < 0` is false.
        simp only [or_false, lt_self_iff_false] at hQ0
        exact absurd trivial hQ0

omit [Fintype Salt] in
/-- **A signing-free continuation cannot increase the collision flag (real flag handler).**
Appending a signing-free continuation `kont` (each `kont x` makes no signing query, e.g. the GPV
verification read) after `oa` does not increase the run-level collision-flag probability of
`gpvRealImplFlag`: the flag fires only on signing steps, so by `gpvRealImplFlag_run_no_sign_flag_eq`
the final flag of the `kont`-run equals the flag at the end of `oa` on every support point (and the
`kont` run may only lose mass on failure).  This is the run-level statement of the off-by-one
resolution: the verification read carries no flag mass. -/
theorem probEvent_flag_bind_no_sign_le [Inhabited Range] (pk : PK) (sk : SK)
    {β γ : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (kont : β → OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (cache : (Salt × M →ₒ Range).QueryCache) (b : Bool)
    (hkont : ∀ x, (kont x).IsQueryBoundP (· matches .inr _) 0) :
    Pr[fun z : γ × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
        (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (oa >>= kont)).run (cache, b)]
      ≤ Pr[fun w : β × ((Salt × M →ₒ Range).QueryCache × Bool) => w.2.2 = true |
        (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] := by
  classical
  rw [simulateQ_bind, StateT.run_bind]
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun w => ?_
  -- Inner event probability is `≤ 1{w.2.2 = true}`: on every support point the flag equals `w.2.2`.
  have hinner :
      Pr[fun z : γ × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (kont w.1)).run w.2]
        ≤ (if w.2.2 = true then 1 else 0) := by
    by_cases hw : w.2.2 = true
    · rw [if_pos hw]; exact probEvent_le_one
    · rw [if_neg hw]
      refine le_of_eq (probEvent_eq_zero_iff.2 (fun z hz => ?_))
      obtain ⟨a, c', b'⟩ := w
      have := gpvRealImplFlag_run_no_sign_flag_eq psf hr M Salt pk sk (kont a) c' b'
        (hkont a) z hz
      simp only [this]
      simpa using hw
  calc Pr[= w | (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] *
        Pr[fun z : γ × ((Salt × M →ₒ Range).QueryCache × Bool) => z.2.2 = true |
            (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (kont w.1)).run w.2]
      ≤ Pr[= w | (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] *
          (if w.2.2 = true then 1 else 0) := by gcongr
    _ = (if w.2.2 = true then
          Pr[= w | (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)]
          else 0) := by
        by_cases hw : w.2.2 = true <;> simp [hw]

open Classical in
/-- **Verify-Bool coupling (fixed key pair).** Running the adversary `adv.main pk` followed by a
signing-free continuation `kont` (the verification read, kept *inside the shared random-oracle
cache*) on the two flag-instrumented original GPV handlers stays within `collisionBound`.

This is the genuine verify-Bool content of the lift: the framework identical-until-bad reduction
`tvDist_simulateQ_run_le_probEvent_output_bad` applies *verbatim* to the verify-extended computation
`adv.main pk >>= kont` (its conclusion keeps the final state, so the verification reads against the
shared cache), bounding the TV by the run-level collision flag.  Because `kont` issues no signing
query, the flag carries no extra mass (`probEvent_flag_bind_no_sign_le`), so the flag probability is
the *same* `collisionBound Salt qSign qHash` as for `adv.main pk` alone
(`gpv_orig_flag_le_collisionBound`) — no `qHash` off-by-one from the verification read. -/
theorem gpv_tvDist_orig_verify_le_collisionBound [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) {γ : Type}
    (kont : M × (Salt × Domain) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hkont : ∀ x, (kont x).IsQueryBoundP (· matches .inr _) 0)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    tvDist ((simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (adv.main pk >>= kont)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), false))
        ((simulateQ (progGameRunImplNoRecFlag psf M Salt domainSample pk)
            (adv.main pk >>= kont)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), false))
      ≤ (collisionBound Salt qSign qHash).toReal := by
  -- Framework identical-until-bad on the verify-extended computation: the conclusion keeps the
  -- final cache, so `kont` reads against the shared random oracle.
  refine le_trans
    (OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
      (gpvRealImplFlag psf hr M Salt pk sk) (progGameRunImplNoRecFlag psf M Salt domainSample pk)
      (adv.main pk >>= kont) (∅ : (Salt × M →ₒ Range).QueryCache)
      (gpvImplFlag_h_agree_good psf hr M Salt pk sk domainSample hNF hreg)
      (gpvRealImplFlag_bad_mono psf hr M Salt pk sk)
      (progGameRunImplNoRecFlag_bad_mono psf M Salt domainSample pk)) ?_
  -- The verify-extended flag probability is ≤ the flag probability of `adv.main pk` alone
  -- (no signing query in `kont`), which the cardinality telescope bounds by `collisionBound`.
  refine ENNReal.toReal_mono ?_ ?_
  · unfold collisionBound
    exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])
  · refine le_trans (probEvent_flag_bind_no_sign_le psf hr M Salt pk sk (adv.main pk) kont
      (∅ : (Salt × M →ₒ Range).QueryCache) false hkont) ?_
    have hreal := gpv_orig_flag_le_collisionBound psf hr M Salt pk sk adv qSign qHash hQ
    have hne : (collisionBound Salt qSign qHash) ≠ ⊤ := by
      unfold collisionBound
      exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])
    exact (ENNReal.toReal_le_toReal probEvent_ne_top hne).mp hreal

/-! ### Freshness-tracking vehicle (the signed-set product factor)

The verify-Bool coupling `gpv_tvDist_orig_verify_le_collisionBound` runs the verification read
inside the shared random-oracle cache, but its vehicle state `QueryCache × Bool` carries no record
of which messages were sent to the *signing* oracle, so a freshness mask cannot be computed on it.
The EUF-CMA forgery winning condition requires the forged message to be *fresh* (never signed); a
replay of a received signature is not a forgery.

The handlers below carry the verify-Bool coupling over a *freshness-tracking* vehicle
with state `(QueryCache × Finset M) × Bool`: the random-oracle cache, a `Finset M` recording the
signed messages, and the salt-collision flag (the unchanged bad event). The signed-set is a
*passive product factor*: each signing step inserts the message identically on both the real and
the programmed handler, and every non-signing step leaves it untouched, so it agrees off-bad and
the flag/telescope are unaffected. The identical-until-bad lemma
`tvDist_simulateQ_run_le_probEvent_output_bad` is generic over the state, so the *same* salt-
collision bad event applies; projecting the signed-set away recovers the original flag run, so the
flag probability — and hence the `collisionBound` — is identical. The verification continuation may
then read the signed-set to apply the freshness mask. -/

omit [DecidableEq Range] [SampleableType Range] [DecidableEq Salt] [SampleableType Salt]
  [Fintype Salt] in
/-- **Flag-and-signed-set tag on a non-signing step output.** Tagging the output of a flagless
underlying step `m : ProbComp (α' × QueryCache)` with a *fixed* signed-set `sgnSet` and a flag `F`
gives the off-bad output probability: `0` if the flag fired, otherwise the signed-set must match
`sgnSet` and the probability reduces to the underlying step. This is the signed-set-carrying
analogue of `probOutput_flagTag_false`, used in the non-signing branch of the fresh
`h_agree_good`. -/
lemma probOutput_flagSignedTag_false {α' : Type}
    (m : ProbComp (α' × (Salt × M →ₒ Range).QueryCache)) (sgnSet sgnSet' : Finset M) (F : Bool)
    (u : α') (c' : (Salt × M →ₒ Range).QueryCache) :
    Pr[= (u, ((c', sgnSet'), false)) |
        ((fun p : α' × (Salt × M →ₒ Range).QueryCache => (p.1, ((p.2, sgnSet), F)))
          <$> m : ProbComp (α' × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))]
      = if F = false ∧ sgnSet' = sgnSet then Pr[= (u, c') | m] else 0 := by
  classical
  rw [probOutput_map_eq_tsum_ite]
  by_cases hF : F = false ∧ sgnSet' = sgnSet
  · obtain ⟨hF0, hFs⟩ := hF
    subst hF0; subst hFs
    rw [if_pos ⟨rfl, rfl⟩, ← tsum_ite_eq (u, c') (fun x => Pr[= x | m])]
    refine tsum_congr fun x => ?_
    congr 1
    rw [eq_iff_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
    constructor
    · rintro ⟨h1, ⟨h2, _⟩, _⟩; exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, ⟨h2.symm, rfl⟩, rfl⟩
  · rw [if_neg hF, ENNReal.tsum_eq_zero]
    intro x
    rw [if_neg]
    rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
    rintro ⟨_, ⟨_, h3⟩, h4⟩
    exact hF ⟨h4.symm, h3⟩

open Classical in
/-- **Flag-instrumented freshness-tracking real handler.** `gpvRealImplFlag` extended with a passive
`Finset M` recording the signed messages. The state is `((QueryCache × Finset M) × Bool)`. Uniform
and random-oracle-read queries leave the signed-set and flag untouched; a signing query draws its
fresh inline salt `r ← $ᵗ Salt`, runs the underlying real signing body on the cache component,
*inserts the message* into the signed-set, and OR-s the collision flag with `saltKeyed`. Projecting
the signed-set away recovers `gpvRealImplFlag`. -/
noncomputable def gpvRealImplFlagFresh (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, ((p.2, s.1.2), s.2))) <$>
          (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), ((p.2, insert msg s.1.2), s.2 || saltKeyed M Salt s.1.1 r))

open Classical in
/-- **Flag-instrumented freshness-tracking programmed handler.** The programmed dual of
`gpvRealImplFlagFresh`: `progGameRunImplNoRecFlag` extended with the same passive signed-set,
inserting the message on each signing step. Projecting the signed-set away recovers
`progGameRunImplNoRecFlag`. -/
noncomputable def progGameRunImplNoRecFlagFresh (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, ((p.2, s.1.2), s.2))) <$>
          (progGameRunImplNoRec psf M Salt domainSample pk (.inl q)).run s.1.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sgn ← (domainSample pk : ProbComp Domain)
        pure ((r, sgn), ((s.1.1.cacheQuery (r, msg) (psf.eval pk sgn), insert msg s.1.2),
          s.2 || saltKeyed M Salt s.1.1 r))

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFlagFresh` on a non-signing query.** -/
lemma gpvRealImplFlagFresh_run_inl (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (gpvRealImplFlagFresh psf hr M Salt pk sk (.inl q)).run s =
      (fun p => (p.1, ((p.2, s.1.2), s.2))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1.1 := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRecFlagFresh` on a non-signing query.** -/
lemma progGameRunImplNoRecFlagFresh_run_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk (.inl q)).run s =
      (fun p => (p.1, ((p.2, s.1.2), s.2))) <$>
        (progGameRunImplNoRec psf M Salt domainSample pk (.inl q)).run s.1.1 := rfl

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFlagFresh` on a signing query.** -/
lemma gpvRealImplFlagFresh_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (gpvRealImplFlagFresh psf hr M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), ((p.2, insert msg s.1.2), s.2 || saltKeyed M Salt s.1.1 r))) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRecFlagFresh` on a signing query.** -/
lemma progGameRunImplNoRecFlagFresh_run_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (msg : M) (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sgn ← (domainSample pk : ProbComp Domain)
        pure ((r, sgn), ((s.1.1.cacheQuery (r, msg) (psf.eval pk sgn), insert msg s.1.2),
          s.2 || saltKeyed M Salt s.1.1 r))) := rfl

omit [Fintype Salt] in
/-- **Per-query signed-set projection of the real fresh flag handler.** Dropping the signed-set
component (`fun s => (s.1.1, s.2)`, keeping the cache and the flag) from one
`gpvRealImplFlagFresh` query step recovers the corresponding `gpvRealImplFlag` step. The signed-set
is a passive auxiliary: it is written by the signing step but never affects the output, the cache,
or the flag, so projecting it away yields the `gpvRealImplFlag` handler. This is the per-query
hypothesis of the state-projection transport `map_run_simulateQ_eq_of_query_map_eq`. -/
lemma gpvRealImplFlagFresh_proj (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2)) <$>
        (gpvRealImplFlagFresh psf hr M Salt pk sk t).run s =
      (gpvRealImplFlag psf hr M Salt pk sk t).run (s.1.1, s.2) := by
  cases t with
  | inl q =>
      rw [gpvRealImplFlagFresh_run_inl, gpvRealImplFlag_run_inl]
      simp only [Functor.map_map, Prod.map, id_eq]
  | inr msg =>
      rw [gpvRealImplFlagFresh_run_inr, gpvRealImplFlag_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-query signed-set projection of the programmed fresh flag handler.** The programmed dual of
`gpvRealImplFlagFresh_proj`: dropping the signed-set recovers `progGameRunImplNoRecFlag`. -/
lemma progGameRunImplNoRecFlagFresh_proj (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2)) <$>
        (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk t).run s =
      (progGameRunImplNoRecFlag psf M Salt domainSample pk t).run (s.1.1, s.2) := by
  cases t with
  | inl q =>
      rw [progGameRunImplNoRecFlagFresh_run_inl, progGameRunImplNoRecFlag_run_inl]
      simp only [Functor.map_map, Prod.map, id_eq]
  | inr msg =>
      rw [progGameRunImplNoRecFlagFresh_run_inr, progGameRunImplNoRecFlag_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [Fintype Salt] in
/-- **Run-level signed-set projection of the real fresh flag handler.** Dropping the signed-set from
the full simulated run of `gpvRealImplFlagFresh` over `oa` recovers the run of `gpvRealImplFlag`.
This transports the per-query projection `gpvRealImplFlagFresh_proj` through
the whole computation via `map_run_simulateQ_eq_of_query_map_eq`, witnessing that the signed-set is
a passive instrument: its addition changes neither the output, the cache, nor the flag. -/
lemma map_run_gpvRealImplFlagFresh_eq (pk : PK) (sk : SK)
    {β : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2)) <$>
        (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run s =
      (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (s.1.1, s.2) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2))
    (gpvRealImplFlagFresh_proj psf hr M Salt pk sk) oa s

omit [Fintype Salt] in
/-- **Bad-monotonicity of the real fresh flag handler.** Once the collision flag is set
(`p.2 = true`), every output of one `gpvRealImplFlagFresh` query step also carries the flag set.
This is the `h_mono` hypothesis of `tvDist_simulateQ_run_le_probEvent_output_bad`. -/
lemma gpvRealImplFlagFresh_bad_mono (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((gpvRealImplFlagFresh psf hr M Salt pk sk t).run p), z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [gpvRealImplFlagFresh_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      rw [gpvRealImplFlagFresh_run_inr] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨r, _, c, _, sgn, _, hw⟩ := hz
      subst hw; simp [hp]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Bad-monotonicity of the programmed fresh flag handler.** -/
lemma progGameRunImplNoRecFlagFresh_bad_mono (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (p : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) (hp : p.2 = true) :
    ∀ z ∈ support ((progGameRunImplNoRecFlagFresh psf M Salt domainSample pk t).run p),
      z.2.2 = true := by
  intro z hz
  cases t with
  | inl q =>
      rw [progGameRunImplNoRecFlagFresh_run_inl] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, _, hw⟩ := hz
      simp [← hw, hp]
  | inr msg =>
      rw [progGameRunImplNoRecFlagFresh_run_inr] at hz
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨r, _, sgn, _, hw⟩ := hz
      subst hw; simp [hp]

omit [Fintype Salt] [DecidableEq Range] [SampleableType Salt] in
/-- **Off-bad joint agreement of the two fresh-vehicle flag signing steps on a fresh inline salt.**
The signed-set-carrying analogue of `evalDist_gpvImplFlag_run_sign_offbad_eq`: with the inline salt
`r` fixed and not yet keyed (`cache (r, msg) = none`, so the flag stays `false`), the full
signing-step body outputs — including the *same* inserted signed-set `insert msg sgnSet` — coincide
in distribution. Both handlers apply the same deterministic post-processing inserting `msg` to the
two `(target, preimage)` draws that coincide by PSF regularity `hreg`. -/
theorem evalDist_gpvImplFlagFresh_run_sign_offbad_eq (pk : PK) (sk : SK)
    (domainSample : PK → ProbComp Domain) (msg : M) (r : Salt) (sgnSet : Finset M)
    (cache : (Salt × M →ₒ Range).QueryCache) (hmiss : cache (r, msg) = none)
    (hreg : 𝒟[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))]) :
    𝒟[(do
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
        let sgn ← psf.trapdoorSample pk sk p.1
        pure (((r, sgn), ((p.2, insert msg sgnSet), false)) :
          (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))]
      = 𝒟[(do
          let sgn ← (domainSample pk : ProbComp Domain)
          pure (((r, sgn),
            ((cache.cacheQuery (r, msg) (psf.eval pk sgn), insert msg sgnSet), false)) :
            (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))] := by
  classical
  -- Reuse the flagless-signed-set signing-miss bridge by post-composing the signed-set insertion.
  set g : (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool) →
      (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :=
    fun z => (z.1, ((z.2.1, insert msg sgnSet), z.2.2)) with hg
  have hbase := evalDist_gpvImplFlag_run_sign_offbad_eq psf M Salt pk sk domainSample
    msg r cache hmiss hreg
  have hL :
      𝒟[(do
          let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
          let sgn ← psf.trapdoorSample pk sk p.1
          pure (((r, sgn), ((p.2, insert msg sgnSet), false)) :
            (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))]
        = 𝒟[g <$> (do
            let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run cache
            let sgn ← psf.trapdoorSample pk sk p.1
            pure (((r, sgn), (p.2, false)) :
              (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))] := by
    simp only [hg, map_bind, map_pure]
  have hR :
      𝒟[(do
          let sgn ← (domainSample pk : ProbComp Domain)
          pure (((r, sgn),
            ((cache.cacheQuery (r, msg) (psf.eval pk sgn), insert msg sgnSet), false)) :
            (Salt × Domain) × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)))]
        = 𝒟[g <$> (do
            let sgn ← (domainSample pk : ProbComp Domain)
            pure (((r, sgn), (cache.cacheQuery (r, msg) (psf.eval pk sgn), false)) :
              (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × Bool)))] := by
    simp only [hg, map_bind, map_pure]
  rw [hL, hR]
  exact evalDist_map_eq_of_evalDist_eq hbase g

omit [Fintype Salt] in
open Classical in
/-- **Universal off-bad per-query agreement of the two fresh-vehicle flag handlers (the framework
`h_agree_good`).** For every query `t` and every off-bad input state `(s, false)` (with
`s : QueryCache × Finset M`), the two fresh flag handlers assign equal probability to every off-bad
output `(u, (s', false))`. This is the signed-set-carrying analogue of `gpvImplFlag_h_agree_good`:
the signed-set is inserted identically on both sides at a signing step and untouched elsewhere, so
that agreement carries over verbatim, with the signing-miss bridge supplied by
`evalDist_gpvImplFlagFresh_run_sign_offbad_eq`. -/
theorem gpvImplFlagFresh_h_agree_good (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let sd ← domainSample pk; pure (psf.eval pk sd, sd)
            : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let sd ← psf.trapdoorSample pk sk c; pure (c, sd)
            : ProbComp (Range × Domain))])
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Finset M)
    (u : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t)
    (s' : (Salt × M →ₒ Range).QueryCache × Finset M) :
    Pr[= (u, (s', false)) | (gpvRealImplFlagFresh psf hr M Salt pk sk t).run (s, false)]
      = Pr[= (u, (s', false)) |
          (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk t).run (s, false)] := by
  cases t with
  | inl q =>
      -- Non-signing query: signed-set and flag are passive; reduce to the underlying agreement.
      rw [gpvRealImplFlagFresh_run_inl, progGameRunImplNoRecFlagFresh_run_inl]
      obtain ⟨c', sgnSet'⟩ := s'
      rw [probOutput_flagSignedTag_false, probOutput_flagSignedTag_false]
      by_cases hsig : sgnSet' = s.2
      · simp only [hsig, and_self, if_pos]
        cases q with
        | inl n =>
            -- Uniform query: the two underlying handlers are literally identical.
            rw [gpvRealImpl_run_unif, progGameRunImplNoRec_run_unif]
        | inr mc =>
            -- Random-oracle read: agree by the underlying read agreement.
            exact probOutput_congr rfl
              (evalDist_gpvImpl_run_read_eq psf hr M Salt pk sk domainSample mc s.1 hNF hreg)
      · simp only [hsig, and_false, if_false]
  | inr msg =>
      -- Signing query: split over the inline salt `r`; keyed `r` ⇒ flag fires ⇒ both `0`;
      -- unkeyed `r` ⇒ flag stays `false`, signed-set inserts `msg`, bodies agree.
      rw [gpvRealImplFlagFresh_run_inr, progGameRunImplNoRecFlagFresh_run_inr]
      simp only [Bool.false_or]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      refine tsum_congr (fun r => ?_)
      refine congrArg _ ?_
      rcases hkey : saltKeyed M Salt s.1 r with _ | _
      · -- Unkeyed salt `r`: flag stays `false`; bodies agree (signed-set inserts `msg` on both).
        have hmiss : s.1 (r, msg) = none := (saltKeyed_eq_false_iff M Salt s.1 r).1 hkey msg
        exact probOutput_congr rfl
          (evalDist_gpvImplFlagFresh_run_sign_offbad_eq psf M Salt pk sk domainSample
            msg r s.2 s.1 hmiss hreg)
      · -- Keyed salt `r`: the flag fires (`true`); the `false`-flag output has probability `0`.
        rw [probOutput_eq_zero_of_not_mem_support, probOutput_eq_zero_of_not_mem_support]
        · intro hmem
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          tauto
        · intro hmem
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem
          tauto

omit [Fintype Salt] in
/-- **Flag-probability projection of the fresh vehicle.** The run-level collision-flag probability
of the fresh handler `gpvRealImplFlagFresh` equals that of the handler `gpvRealImplFlag`:
the signed-set is passive, so projecting it away (`map_run_gpvRealImplFlagFresh_eq`) preserves the
flag (which lives in the retained `Bool` component). This is the bridge that lets the
cardinality telescope `gpv_orig_flag_le_collisionBound` bound the fresh flag at the *same*
`collisionBound`. -/
lemma probEvent_flag_gpvRealImplFlagFresh_eq (pk : PK) (sk : SK)
    {β : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (cache : (Salt × M →ₒ Range).QueryCache) (sgnSet : Finset M) (b : Bool) :
    Pr[fun z : β × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) => z.2.2 = true |
        (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run ((cache, sgnSet), b)]
      = Pr[fun w : β × ((Salt × M →ₒ Range).QueryCache × Bool) => w.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] := by
  have hmap := map_run_gpvRealImplFlagFresh_eq psf hr M Salt pk sk oa ((cache, sgnSet), b)
  calc Pr[fun z : β × (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) => z.2.2 = true |
        (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run ((cache, sgnSet), b)]
      = Pr[fun w : β × ((Salt × M →ₒ Range).QueryCache × Bool) => w.2.2 = true |
          (Prod.map id
            (fun s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool => (s.1.1, s.2))) <$>
            (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run
              ((cache, sgnSet), b)] := by
        rw [probEvent_map]; rfl
    _ = Pr[fun w : β × ((Salt × M →ₒ Range).QueryCache × Bool) => w.2.2 = true |
          (simulateQ (gpvRealImplFlag psf hr M Salt pk sk) oa).run (cache, b)] := by
        rw [hmap]

open Classical in
/-- **Verify-Bool coupling on the freshness-tracking vehicle (fixed key pair).** Running the
adversary `adv.main pk` followed by a signing-free continuation `kont` (the verification read, kept
*inside the shared random-oracle cache* and now able to read the signed-set for the freshness mask)
on the two *fresh* flag-instrumented GPV handlers stays within `collisionBound`.

This re-derives `gpv_tvDist_orig_verify_le_collisionBound` over the freshness-tracking vehicle
`gpvRealImplFlagFresh` / `progGameRunImplNoRecFlagFresh` (state `(QueryCache × Finset M) × Bool`):
the framework identical-until-bad reduction `tvDist_simulateQ_run_le_probEvent_output_bad` applies
*verbatim* to the verify-extended computation `adv.main pk >>= kont` (its conclusion keeps the final
state, so the verification reads against the shared cache *and* the shared signed-set), bounding the
TV by the run-level collision flag.  Because `kont` issues no signing query, the flag carries no
extra mass; projecting the passive signed-set away (`probEvent_flag_gpvRealImplFlagFresh_eq`)
reduces the fresh flag probability to the `gpvRealImplFlag` flag probability, bounded by the *same*
`collisionBound Salt qSign qHash` via `probEvent_flag_bind_no_sign_le` and
`gpv_orig_flag_le_collisionBound` — no `qHash` off-by-one from the verification read.

Unlike the frozen `gpv_tvDist_orig_verify_le_collisionBound`, the vehicle now carries the signed-set
factor, so `kont` may compute the EUF-CMA freshness mask (the forged message not being among the
signed messages) while staying within the same collision bound. -/
theorem gpv_tvDist_orig_verify_fresh_le_collisionBound [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) {γ : Type}
    (kont : M × (Salt × Domain) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) γ)
    (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hkont : ∀ x, (kont x).IsQueryBoundP (· matches .inr _) 0)
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    tvDist ((simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) (adv.main pk >>= kont)).run
          (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false))
        ((simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
            (adv.main pk >>= kont)).run
          (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false))
      ≤ (collisionBound Salt qSign qHash).toReal := by
  -- Framework identical-until-bad on the verify-extended computation over the fresh vehicle.
  refine le_trans
    (OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
      (gpvRealImplFlagFresh psf hr M Salt pk sk)
      (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
      (adv.main pk >>= kont) ((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M))
      (gpvImplFlagFresh_h_agree_good psf hr M Salt pk sk domainSample hNF hreg)
      (gpvRealImplFlagFresh_bad_mono psf hr M Salt pk sk)
      (progGameRunImplNoRecFlagFresh_bad_mono psf M Salt domainSample pk)) ?_
  -- Project the passive signed-set away, reducing the fresh flag to the `gpvRealImplFlag` flag,
  -- then bound the verify-extended flag by `collisionBound` (signing-free `kont` adds no flag).
  refine ENNReal.toReal_mono ?_ ?_
  · unfold collisionBound
    exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])
  · rw [probEvent_flag_gpvRealImplFlagFresh_eq psf hr M Salt pk sk (adv.main pk >>= kont)
      (∅ : (Salt × M →ₒ Range).QueryCache) (∅ : Finset M) false]
    refine le_trans (probEvent_flag_bind_no_sign_le psf hr M Salt pk sk (adv.main pk) kont
      (∅ : (Salt × M →ₒ Range).QueryCache) false hkont) ?_
    have hreal := gpv_orig_flag_le_collisionBound psf hr M Salt pk sk adv qSign qHash hQ
    have hne : (collisionBound Salt qSign qHash) ≠ ⊤ := by
      unfold collisionBound
      exact ENNReal.div_ne_top (by simp) (by simp [Fintype.card_ne_zero])
    exact (ENNReal.toReal_le_toReal probEvent_ne_top hne).mp hreal

open Classical in
/-- **Flag-free freshness-tracking real handler.** `gpvRealImplFlagFresh` with the passive
salt-collision `Bool` flag removed, leaving the state `(QueryCache × Finset M)`. The signing step
draws its fresh inline salt, runs the real signing body on the cache, and inserts the message into
the signed-set; non-signing queries leave the signed-set untouched. Projecting the flag away from
`gpvRealImplFlagFresh` recovers this handler.  Because the winning Bool of the freshness verify
games (`decide (msg ∉ signedSet) && verified`) never reads the flag, the flag-free vehicle carries
exactly the information the game observes. -/
noncomputable def gpvRealImplFresh (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × Finset M) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl q =>
        (fun p => (p.1, (p.2, s.2))) <$>
          (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), (p.2, insert msg s.2))

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFresh` on a non-signing query.** -/
lemma gpvRealImplFresh_run_inl (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Finset M) :
    (gpvRealImplFresh psf hr M Salt pk sk (.inl q)).run s =
      (fun p => (p.1, (p.2, s.2))) <$>
        (gpvRealImpl psf hr M Salt pk sk (.inl q)).run s.1 := rfl

omit [Fintype Salt] in
/-- **One-step unfolding of `gpvRealImplFresh` on a signing query.** -/
lemma gpvRealImplFresh_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × Finset M) :
    (gpvRealImplFresh psf hr M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let p ← (randomOracle (spec := (Salt × M →ₒ Range)) (r, msg)).run s.1
        let sgn ← psf.trapdoorSample pk sk p.1
        pure ((r, sgn), (p.2, insert msg s.2))) := rfl

omit [Fintype Salt] in
/-- **Per-query flag projection of the fresh flag handler.** Dropping the passive collision flag
(`Prod.map id Prod.fst`, keeping the cache and the signed-set) from one `gpvRealImplFlagFresh` query
step recovers the corresponding `gpvRealImplFresh` step. The flag is written by the signing step but
never affects the output, the cache, or the signed-set, so projecting it away yields the flag-free
fresh handler. This is the per-query hypothesis of the state-projection transport
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma gpvRealImplFlagFresh_proj_flag (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool →
        (Salt × M →ₒ Range).QueryCache × Finset M) <$>
        (gpvRealImplFlagFresh psf hr M Salt pk sk t).run s =
      (gpvRealImplFresh psf hr M Salt pk sk t).run s.1 := by
  cases t with
  | inl q =>
      rw [gpvRealImplFlagFresh_run_inl, gpvRealImplFresh_run_inl]
      simp only [Functor.map_map, Prod.map, id_eq]
  | inr msg =>
      rw [gpvRealImplFlagFresh_run_inr, gpvRealImplFresh_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [Fintype Salt] in
/-- **Run-level flag projection of the fresh flag handler.** Dropping the collision flag from the
full simulated run of `gpvRealImplFlagFresh` over `oa` recovers the run of the flag-free handler
`gpvRealImplFresh`. Transports the per-query `gpvRealImplFlagFresh_proj_flag` through the whole
computation via `map_run_simulateQ_eq_of_query_map_eq`: the flag is a passive instrument. -/
lemma map_run_gpvRealImplFlagFresh_proj_flag (pk : PK) (sk : SK) {β : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool →
        (Salt × M →ₒ Range).QueryCache × Finset M) <$>
        (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) oa).run s =
      (simulateQ (gpvRealImplFresh psf hr M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool →
      (Salt × M →ₒ Range).QueryCache × Finset M)
    (gpvRealImplFlagFresh_proj_flag psf hr M Salt pk sk) oa s

/-! ### Stage-4 combined handler: programmed game ⊕ collision reduction

The distinct-collision transfer needs to relate the programmed freshness game handler
`progGameRunImplNoRecFlagFresh` (state `((cache × signedSet) × flag)`) to the collision
`reduction`'s internal handler (state `cache × table`, where `table : (Salt × M) → Option Domain`
records, for each programmed point, the hidden short preimage `s` used to define the random-oracle
value `psf.eval pk s` there). The reduction's handler is *not* a projection of the game handler: on
a random-oracle miss it draws `s ← domainSample pk`, caches `psf.eval pk s`, and stores `s` in the
table — and `s` is not recoverable from `psf.eval pk s` (`eval` is many-to-one).

The resolution is to build a single **combined** handler `progGameRunImplCombined` that draws each
programmed preimage `s` *once* and updates every component (cache, signed-set, flag, and the hidden
table) in one step, exactly matching the draw order of both games. It then projects definitionally
onto each:

* dropping the table recovers `progGameRunImplNoRecFlagFresh`
  (`map_run_progGameRunImplCombined_proj_table`);
* dropping the signed-set and the flag recovers the reduction's internal handler `reductionImpl`
  (`map_run_progGameRunImplCombined_proj_reduction`).

A support invariant (`progGameRunImplCombined_run_inv`) records that the table and the cache stay
coherent: at every programmed point `t`, `table t = some d → cache t = some (psf.eval pk d)`. -/

open Classical in
/-- **The collision reduction's internal oracle handler.** The named handler stack
`(unifImpl + roImpl) + signImpl` over `StateT (QueryCache × ((Salt × M) → Option Domain)) ProbComp`
that the collision `reduction` runs the adversary under. On a random-oracle miss it forward-samples
a short preimage `s ← domainSample pk`, sets the cache value to `psf.eval pk s`, and records `s` in
the hidden table at the queried point; the signing handler does the same at the freshly salted point
`(r, msg)`. Cache hits and uniform queries leave the table untouched. The reduction's body equals
running the adversary under this handler from `(∅, fun _ => none)` and reading the hidden preimage
off the final table (`reduction_eq_run_reductionImpl`). -/
noncomputable def reductionImpl (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)) ProbComp) :=
  let State := (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let s ← (domainSample pk : ProbComp Domain)
          let v := psf.eval pk s
          set ((st.1.cacheQuery t v, fun t' => if t' = t then some s else st.2 t') : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let s ← (domainSample pk : ProbComp Domain)
      let v := psf.eval pk s
      let st ← get
      set ((st.1.cacheQuery (r, msg) v,
        fun t' => if t' = (r, msg) then some s else st.2 t') : State)
      pure (r, s)
  (unifImpl + roImpl) + signImpl

omit [Fintype Salt] in
/-- **The collision reduction is `reductionImpl` run from the empty state.** Restates the body of
`reduction` in terms of the named internal handler `reductionImpl`: run the adversary under
`reductionImpl` from `(∅, fun _ => none)`, then read the hidden programmed preimage off the final
table at the forged point. The two are definitionally equal — `reduction`'s `let impl := …` block
*is* `reductionImpl`. -/
lemma reduction_eq_run_reductionImpl
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    reduction psf hr M Salt adv domainSample pk =
      (do
        let ((msgStar, (_rStar, sStar)), st) ←
          (simulateQ (reductionImpl psf M Salt domainSample pk) (adv.main pk)).run
            (∅, fun _ => none)
        match st.2 (_rStar, msgStar) with
        | some sHidden => pure (sHidden, sStar)
        | none => pure (sStar, sStar)) := rfl

/-- **Pre-sampled-index programmed-preimage handler.** Embeds the external target `y` at the
`w`-th programmed random-oracle entry (counting RO-query programming steps), caching `psf.eval pk s`
at every other entry and at every signing entry, and NEVER overwriting an already-cached slot. The
embed index `w` is fixed before the run, so the simulated random oracle is consistent under
re-query. Signing entries always return a valid signature `(r, s)` with `psf.eval pk s` the cached
value. -/
noncomputable def embedAtIndexImpl (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × ℕ) ProbComp) :=
  let State := (Salt × M →ₒ Range).QueryCache × ℕ
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let s ← (domainSample pk : ProbComp Domain)
          if st.2 = w then
            set ((st.1.cacheQuery t y, st.2 + 1) : State)
            pure y
          else
            set ((st.1.cacheQuery t (psf.eval pk s), st.2 + 1) : State)
            pure (psf.eval pk s)
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let s ← (domainSample pk : ProbComp Domain)
      let st ← get
      set ((st.1.cacheQuery (r, msg) (psf.eval pk s), st.2 + 1) : State)
      pure (r, s)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- One-step unfolding of `embedAtIndexImpl` on a uniform query. -/
lemma embedAtIndexImpl_run_inl_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) (q : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    (embedAtIndexImpl psf M Salt domainSample pk w y (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- One-step unfolding of `embedAtIndexImpl` on a random-oracle query. -/
lemma embedAtIndexImpl_run_inl_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) (q : (Salt × M →ₒ Range).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedAtIndexImpl psf M Salt domainSample pk w y (.inl (.inr q))).run s :
        ProbComp (Range × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (match s.1 q with
        | some v => pure (v, s)
        | none =>
            (fun sd : Domain =>
              (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
               else (psf.eval pk sd, (s.1.cacheQuery q (psf.eval pk sd), s.2 + 1)) :
                Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
              <$> (domainSample pk : ProbComp Domain)) := by
  cases hq : s.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedAtIndexImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply]
      refine bind_congr fun sd => ?_
      split_ifs with hb <;> simp [StateT.run_set]
  | some v =>
      simp [embedAtIndexImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- One-step unfolding of `embedAtIndexImpl` on a signing query. -/
lemma embedAtIndexImpl_run_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) (msg : M) (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedAtIndexImpl psf M Salt domainSample pk w y (.inr msg)).run s :
        ProbComp ((Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        (fun sd : Domain =>
          ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), s.2 + 1)) :
            Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
          <$> (domainSample pk : ProbComp Domain)) := by
  simp only [add_apply_inr, embedAtIndexImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

/-- **Trapdoor-uniform sibling of the pre-sampled-index handler.** Same state `cache × ℕ`, counter
logic, and never-overwrite discipline as `embedAtIndexImpl`, but every cached image is drawn
*uniformly* rather than as `psf.eval pk s`:

* on a non-winner random-oracle miss (`count ≠ w`) it caches a uniform `v ← $ᵗ Range` and returns
  `v` (output equals the cached value, as in `embedAtIndexImpl`);
* at the winner random-oracle miss (`count = w`) it still embeds the external target `y`;
* on a signing query it draws a uniform image `c ← $ᵗ Range`, caches `c`, and returns the
  *trapdoor preimage* `x ← psf.trapdoorSample pk sk c` as the signature's domain component.

Per-step this handler is equidistributed with `embedAtIndexImpl` under GPV regularity `hreg`
(`evalDist_embedAtIndex_step_eq_embedTrap`).  On a uniform query and on a random-oracle cache hit
the two handlers are literally identical.  On a non-winner random-oracle miss the only difference is
the cached/returned image, whose marginal law `hreg` equates (`psf.eval pk s ≡ $ᵗ Range`).  On a
signing step the joint law of the `(returned domain component, cached image)` pair is
`(s, psf.eval pk s)` for `s ← domainSample pk` on the `embedAtIndexImpl` side versus
`(psf.trapdoorSample pk sk c, c)` for `c ← $ᵗ Range` on this side — the two sides of `hreg`.

Threaded through the adaptive fold by the same-state engine
(`evalDist_run_embedAtIndexImpl_eq_embedTrap`), it makes the embed run an all-uniform consistent
random oracle (modulo `y` at the winner), matching the trapdoor-recording combined run's cache. -/
noncomputable def embedTrapImpl (pk : PK) (sk : SK)
    (w : ℕ) (y : Range) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × ℕ) ProbComp) :=
  let State := (Salt × M →ₒ Range).QueryCache × ℕ
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          if st.2 = w then
            set ((st.1.cacheQuery t y, st.2 + 1) : State)
            pure y
          else
            set ((st.1.cacheQuery t v, st.2 + 1) : State)
            pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set ((st.1.cacheQuery (r, msg) c, st.2 + 1) : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapImpl` on a uniform query. -/
lemma embedTrapImpl_run_inl_inl (pk : PK) (sk : SK)
    (w : ℕ) (y : Range) (q : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    (embedTrapImpl psf M Salt pk sk w y (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapImpl` on a random-oracle query. -/
lemma embedTrapImpl_run_inl_inr (pk : PK) (sk : SK)
    (w : ℕ) (y : Range) (q : (Salt × M →ₒ Range).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedTrapImpl psf M Salt pk sk w y (.inl (.inr q))).run s :
        ProbComp (Range × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (match s.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
               else (v, (s.1.cacheQuery q v, s.2 + 1)) :
                Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply]
      refine bind_congr fun v => ?_
      split_ifs with hb <;> simp [StateT.run_set]
  | some v =>
      simp [embedTrapImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapImpl` on a signing query. -/
lemma embedTrapImpl_run_inr (pk : PK) (sk : SK)
    (w : ℕ) (y : Range) (msg : M) (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedTrapImpl psf M Salt pk sk w y (.inr msg)).run s :
        ProbComp ((Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), (s.1.cacheQuery (r, msg) c, s.2 + 1)) :
              Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **N3 — per-step equidistribution of `embedAtIndexImpl` and `embedTrapImpl`.** For every query
`t` and every embed state `s`, the two handlers produce *equal output distributions* on the same
state `s`, under GPV regularity `hreg` and trapdoor totality `hNF` at `(pk, sk)`.

On a uniform query and on a random-oracle cache *hit* the two handlers are literally identical.  On
a non-winner random-oracle *miss* the only difference is the cached/returned image, equated by the
first marginal of `hreg` (`psf.eval pk s ≡ $ᵗ Range`); the discarded trapdoor draw on the
`$ᵗ Range` side collapses by `hNF`.  At the winner random-oracle miss both handlers embed `y` and
discard the drawn image, so they agree.  On a signing step the joint law of the
`(returned domain component, cached image)` pair is `(s, psf.eval pk s)` for `s ← domainSample pk`
on the `embedAtIndexImpl` side versus `(psf.trapdoorSample pk sk c, c)` for `c ← $ᵗ Range` on the
`embedTrapImpl` side — the two sides of `hreg`, mapped through the (deterministic) cache update.
This is the local hypothesis of `evalDist_simulateQ_run_eq_of_impl_evalDist_eq`. -/
lemma evalDist_embedAtIndex_step_eq_embedTrap
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (w : ℕ) (y : Range)
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    𝒟[(embedAtIndexImpl psf M Salt domainSample pk w y t).run s] =
      𝒟[(embedTrapImpl psf M Salt pk sk w y t).run s] := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedAtIndexImpl_run_inl_inl, embedTrapImpl_run_inl_inl]
      | inr q =>
          rw [embedAtIndexImpl_run_inl_inr, embedTrapImpl_run_inl_inr]
          cases hq : s.1 q with
          | some v => rfl
          | none =>
              -- Random-oracle miss: the cached/returned image is a function of `psf.eval pk sd`
              -- alone, so the first marginal of `hreg` (collapsed by `hNF`) suffices.
              have hfst : 𝒟[(domainSample pk : ProbComp Domain) >>= fun sd =>
                    (pure (psf.eval pk sd) : ProbComp Range)]
                  = 𝒟[($ᵗ Range : ProbComp Range)] :=
                evalDist_eval_domainSample_eq_uniform psf pk sk domainSample hNF hreg
              calc 𝒟[(fun sd : Domain =>
                      (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
                       else (psf.eval pk sd, (s.1.cacheQuery q (psf.eval pk sd), s.2 + 1)) :
                        Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
                    <$> (domainSample pk : ProbComp Domain)]
                  = 𝒟[(fun v : Range =>
                      (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
                       else (v, (s.1.cacheQuery q v, s.2 + 1)) :
                        Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
                    <$> ((domainSample pk : ProbComp Domain) >>= fun sd =>
                      (pure (psf.eval pk sd) : ProbComp Range))] := by
                      rw [map_bind, map_eq_bind_pure_comp]
                      simp only [map_pure, Function.comp_def]
                _ = 𝒟[(fun v : Range =>
                      (if s.2 = w then (y, (s.1.cacheQuery q y, s.2 + 1))
                       else (v, (s.1.cacheQuery q v, s.2 + 1)) :
                        Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
                    <$> ($ᵗ Range : ProbComp Range)] := by
                      rw [evalDist_map, evalDist_map, hfst]
  | inr msg =>
      rw [embedAtIndexImpl_run_inr, embedTrapImpl_run_inr]
      refine evalDist_bind_congr fun r _ => ?_
      -- The `(returned domain component, cached image)` joint is `(sd, eval sd)` vs
      -- `(trapdoorSample c, c)` — the two sides of `hreg`, mapped through the cache update.
      have h := congrArg (Functor.map
        (fun p : Range × Domain =>
          ((r, p.2), (s.1.cacheQuery (r, msg) p.1, s.2 + 1)) :
            Range × Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))) hreg
      simp only [← evalDist_map, map_bind, map_pure] at h
      calc 𝒟[(fun sd : Domain =>
              ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), s.2 + 1)) :
                Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
            <$> (domainSample pk : ProbComp Domain)]
          = 𝒟[(domainSample pk : ProbComp Domain) >>= fun sd =>
              pure ((r, sd), (s.1.cacheQuery (r, msg) (psf.eval pk sd), s.2 + 1))] := by
              rw [map_eq_bind_pure_comp]; rfl
        _ = 𝒟[($ᵗ Range : ProbComp Range) >>= fun c =>
              (psf.trapdoorSample pk sk c : ProbComp Domain) >>= fun x =>
                pure ((r, x), (s.1.cacheQuery (r, msg) c, s.2 + 1))] := h
        _ = 𝒟[($ᵗ Range : ProbComp Range) >>= fun c =>
              (fun x : Domain =>
                ((r, x), (s.1.cacheQuery (r, msg) c, s.2 + 1)) :
                  Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
                <$> (psf.trapdoorSample pk sk c : ProbComp Domain)] := by
              refine evalDist_bind_congr fun c _ => ?_
              rw [map_eq_bind_pure_comp]; rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **N4 — run-level equidistribution of `embedAtIndexImpl` and `embedTrapImpl`.** For *any*
adaptive computation `oa` and any start embed state `s`, the full simulated run of the
pre-sampled-index handler `embedAtIndexImpl` over `oa` is *equidistributed* with the run of its
trapdoor-uniform sibling `embedTrapImpl`, under GPV regularity `hreg` and trapdoor totality `hNF`.

The two handlers agree query-by-query as output distributions on the same embed state
(`evalDist_embedAtIndex_step_eq_embedTrap`); the same-state distributional simulation engine
`evalDist_simulateQ_run_eq_of_impl_evalDist_eq` threads that per-step equality through the entire
adaptive fold.  After this rewrite the embed run is an all-uniform consistent random oracle (modulo
the embedded target `y` at the winner slot), so its cache marginal coincides with the cache of the
trapdoor-recording combined run `progGameRunImplCombinedTrap`. -/
lemma evalDist_run_embedAtIndexImpl_eq_embedTrap {β : Type}
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (w : ℕ) (y : Range)
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    𝒟[(simulateQ (embedAtIndexImpl psf M Salt domainSample pk w y) oa).run s] =
      𝒟[(simulateQ (embedTrapImpl psf M Salt pk sk w y) oa).run s] :=
  evalDist_simulateQ_run_eq_of_impl_evalDist_eq
    (embedAtIndexImpl psf M Salt domainSample pk w y)
    (embedTrapImpl psf M Salt pk sk w y)
    (evalDist_embedAtIndex_step_eq_embedTrap psf M Salt domainSample pk sk w y hreg hNF) oa s

open Classical in
/-- **The combined programmed-game ⊕ collision-reduction handler.** A single handler that threads
the programmed freshness-game state `((cache × signedSet) × flag)` *together with* the collision
reduction's hidden preimage table `table : (Salt × M) → Option Domain`. Each programming step draws
the short preimage `s ← domainSample pk` *once* and uses it for both the game cache value
`psf.eval pk s` and the table record `s` at the programmed point, exactly matching the draw order of
`progGameRunImplNoRecFlagFresh` and `reductionImpl`.

* `.inl (.inl q)` (uniform): answer from `unifSpec`; cache, signed-set, flag, and table untouched.
* `.inl (.inr q)` (random-oracle read at `q`): on a hit reuse the cached value (table untouched); on
  a miss draw `s`, set the cache to `psf.eval pk s` and the table to `s` at `q`.
* `.inr msg` (signing): draw a fresh salt `r`, draw `s`, set the cache at `(r, msg)` to
  `psf.eval pk s`, insert `msg` into the signed-set, OR the collision flag with `saltKeyed`, and
  record `s` in the table at `(r, msg)`.

Dropping the table recovers `progGameRunImplNoRecFlagFresh`; dropping the signed-set and flag
recovers `reductionImpl`. -/
noncomputable def progGameRunImplCombined (domainSample : PK → ProbComp Domain) (pk : PK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain))) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl (.inl q) => do
        let v ← (unifSpec.query q : ProbComp _)
        pure (v, s)
    | .inl (.inr q) =>
        match s.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let sd ← (domainSample pk : ProbComp Domain)
            pure (psf.eval pk sd,
              (((s.1.1.1.cacheQuery q (psf.eval pk sd), s.1.1.2), s.1.2),
                fun t' => if t' = q then some sd else s.2 t'))
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sd ← (domainSample pk : ProbComp Domain)
        pure ((r, sd),
          (((s.1.1.1.cacheQuery (r, msg) (psf.eval pk sd), insert msg s.1.1.2),
            s.1.2 || saltKeyed M Salt s.1.1.1 r),
            fun t' => if t' = (r, msg) then some sd else s.2 t'))

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombined` on a uniform query.** -/
lemma progGameRunImplCombined_run_inl_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : unifSpec.Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombined psf M Salt domainSample pk (.inl (.inl q))).run s =
      (do let v ← (unifSpec.query q : ProbComp _); pure (v, s)) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombined` on a random-oracle query.** -/
lemma progGameRunImplCombined_run_inl_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (Salt × M →ₒ Range).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombined psf M Salt domainSample pk (.inl (.inr q))).run s =
      (match s.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let sd ← (domainSample pk : ProbComp Domain)
            pure (psf.eval pk sd,
              (((s.1.1.1.cacheQuery q (psf.eval pk sd), s.1.1.2), s.1.2),
                fun t' => if t' = q then some sd else s.2 t'))) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombined` on a signing query.** -/
lemma progGameRunImplCombined_run_inr (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombined psf M Salt domainSample pk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sd ← (domainSample pk : ProbComp Domain)
        pure ((r, sd),
          (((s.1.1.1.cacheQuery (r, msg) (psf.eval pk sd), insert msg s.1.1.2),
            s.1.2 || saltKeyed M Salt s.1.1.1 r),
            fun t' => if t' = (r, msg) then some sd else s.2 t'))) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `reductionImpl` on a uniform query.** -/
lemma reductionImpl_run_inl_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)) :
    (reductionImpl psf M Salt domainSample pk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `reductionImpl` on a random-oracle query.** -/
lemma reductionImpl_run_inl_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (Salt × M →ₒ Range).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)) :
    (reductionImpl psf M Salt domainSample pk (.inl (.inr q))).run s =
      (match s.1 q with
        | some v => pure (v, s)
        | none => do
            let sd ← (domainSample pk : ProbComp Domain)
            pure (psf.eval pk sd,
              (s.1.cacheQuery q (psf.eval pk sd),
                fun t' => if t' = q then some sd else s.2 t'))) := by
  cases hq : s.1 q with
  | none =>
      simp [reductionImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, StateT.run_set, bind_assoc, map_eq_bind_pure_comp, hq]
  | some v =>
      simp [reductionImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, hq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `reductionImpl` on a signing query.** -/
lemma reductionImpl_run_inr (domainSample : PK → ProbComp Domain) (pk : PK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)) :
    (reductionImpl psf M Salt domainSample pk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let sd ← (domainSample pk : ProbComp Domain)
        pure ((r, sd),
          (s.1.cacheQuery (r, msg) (psf.eval pk sd),
            fun t' => if t' = (r, msg) then some sd else s.2 t'))) := by
  simp only [reductionImpl, QueryImpl.add_apply_inr]
  simp [StateT.run_bind, StateT.run_get, StateT.run_set, bind_assoc, map_eq_bind_pure_comp]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a uniform query.** -/
lemma progGameRunImplNoRec_run_inl_inl (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : unifSpec.Domain) (s : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplNoRec` on a random-oracle query.** -/
lemma progGameRunImplNoRec_run_inl_inr (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : (Salt × M →ₒ Range).Domain) (s : (Salt × M →ₒ Range).QueryCache) :
    (progGameRunImplNoRec psf M Salt domainSample pk (.inl (.inr q))).run s =
      (match s q with
        | some v => pure (v, s)
        | none => do
            let sd ← (domainSample pk : ProbComp Domain)
            pure (psf.eval pk sd, s.cacheQuery q (psf.eval pk sd))) := by
  cases hq : s q with
  | none =>
      simp [progGameRunImplNoRec, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, StateT.run_set, bind_assoc, map_eq_bind_pure_comp, hq]
  | some v =>
      simp [progGameRunImplNoRec, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, StateT.run_bind,
        StateT.run_get, hq]

/-! #### D2. Projection of the combined handler onto the programmed game handler

Dropping the hidden preimage table (`proj = Prod.fst`) from the combined handler recovers the
programmed freshness-game handler `progGameRunImplNoRecFlagFresh`. The table is a passive auxiliary
over the game state: every game-state update (cache, signed-set, flag) is performed identically by
both handlers from the *same* drawn preimage, so projecting the table away commutes with each step
and hence with the whole simulation. -/

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-query table projection of the combined handler.** Dropping the hidden table component
(`Prod.fst`, keeping the game state `((cache × signedSet) × flag)`) from one
`progGameRunImplCombined` query step recovers the corresponding `progGameRunImplNoRecFlagFresh`
step. This is the per-query hypothesis of the state-projection transport
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma progGameRunImplCombined_proj_table (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prod.map id
        (Prod.fst : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
          ((Salt × M) → Option Domain) → ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) <$>
        (progGameRunImplCombined psf M Salt domainSample pk t).run s =
      (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl, progGameRunImplNoRecFlagFresh_run_inl,
            progGameRunImplNoRec_run_inl_inl]
          rfl
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr, progGameRunImplNoRecFlagFresh_run_inl,
            progGameRunImplNoRec_run_inl_inr]
          cases s.1.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => rfl
  | inr msg =>
      rw [progGameRunImplCombined_run_inr, progGameRunImplNoRecFlagFresh_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Run-level table projection of the combined handler.** Dropping the hidden preimage table from
the full simulated run of `progGameRunImplCombined` over `oa` recovers the run of the programmed
game handler `progGameRunImplNoRecFlagFresh`. Transports the per-query
`progGameRunImplCombined_proj_table` through the whole computation via
`map_run_simulateQ_eq_of_query_map_eq`: the table is a passive instrument over the game state. -/
lemma map_run_progGameRunImplCombined_proj_table (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prod.map id
        (Prod.fst : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
          ((Salt × M) → Option Domain) → ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) <$>
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s =
      (simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
      ((Salt × M) → Option Domain) → ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)
    (progGameRunImplCombined_proj_table psf M Salt domainSample pk) oa s

/-! #### D2′. Write-only-table deferral: the `eval→trapdoor-recording` run rewrite

The combined handler `progGameRunImplCombined` writes the drawn short preimage `sd` into the hidden
table at each programming step, but it never *reads* that table during the run: every query answer
and every cache write uses only the *image* `psf.eval pk sd`, and the table is consulted only once,
at the final exact-match check.  The table is therefore *write-only* over the entire fold.

This lets the recorded preimage be re-coupled to its already-exposed image by the GPV regularity
`hreg`, target-by-target, without any adaptive interaction.  Concretely, define a sibling handler
`progGameRunImplCombinedTrap` that is identical except that at each programming step it draws the
*image* `v ← $ᵗ Range` uniformly, caches `v`, and records the *trapdoor* preimage
`trapdoorSample pk sk v` of that image in the table.  The two handlers agree query-by-query as
output *distributions* on the **same** state: the only difference is the joint law of the
`(cached image, recorded preimage)` pair, which is `(psf.eval pk sd, sd)` for `sd ← domainSample pk`
on one side and `(v, trapdoorSample pk sk v)` for `v ← $ᵗ Range` on the other — exactly the two
sides of `hreg`.  Mapping `hreg` through the (deterministic) cache/table update establishes the
per-step distributional equality for *any* update, and the distributional simulation engine
`evalDist_simulateQ_run_eq_of_impl_evalDist_eq` threads it through the whole adaptive fold as an
exact equidistribution — no pointwise coupling between the two runs' successor states is required.

This is the clean *end-deferral* underlying the GPV Step-2 reservoir close: the recorded preimage is
re-expressed as the trapdoor preimage of the cached image, matching the reservoir reduction's
challenger preimage of the embedded uniform target. -/

open Classical in
/-- **The trapdoor-recording combined handler.** Identical to `progGameRunImplCombined` except that
each programming step draws the random-oracle *image* `v ← $ᵗ Range` uniformly, caches `v`, and
records the *trapdoor* preimage `x ← psf.trapdoorSample pk sk v` of that image in the hidden table.

Because the recorded preimage is never read during the run (the table is write-only, see
`map_run_progGameRunImplCombined_proj_table`), this handler is equidistributed run-for-run with
`progGameRunImplCombined` under GPV regularity `hreg`
(`evalDist_run_progGameRunImplCombinedTrap_eq`): the only per-step difference is the joint law of
the `(cached image, recorded preimage)` pair, which `hreg` equates. -/
noncomputable def progGameRunImplCombinedTrap (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain))) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl (.inl q) => do
        let v ← (unifSpec.query q : ProbComp _)
        pure (v, s)
    | .inl (.inr q) =>
        match s.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let v ← ($ᵗ Range : ProbComp Range)
            let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
            pure (v,
              (((s.1.1.1.cacheQuery q v, s.1.1.2), s.1.2),
                fun t' => if t' = q then some x else s.2 t'))
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let v ← ($ᵗ Range : ProbComp Range)
        let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
        pure ((r, x),
          (((s.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.2),
            s.1.2 || saltKeyed M Salt s.1.1.1 r),
            fun t' => if t' = (r, msg) then some x else s.2 t'))

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrap` on a uniform query.** -/
lemma progGameRunImplCombinedTrap_run_inl_inl (pk : PK)
    (sk : SK) (q : unifSpec.Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombinedTrap psf M Salt pk sk (.inl (.inl q))).run s =
      (do let v ← (unifSpec.query q : ProbComp _); pure (v, s)) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrap` on a random-oracle query.** -/
lemma progGameRunImplCombinedTrap_run_inl_inr (pk : PK)
    (sk : SK) (q : (Salt × M →ₒ Range).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombinedTrap psf M Salt pk sk (.inl (.inr q))).run s =
      (match s.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let v ← ($ᵗ Range : ProbComp Range)
            let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
            pure (v,
              (((s.1.1.1.cacheQuery q v, s.1.1.2), s.1.2),
                fun t' => if t' = q then some x else s.2 t'))) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrap` on a signing query.** -/
lemma progGameRunImplCombinedTrap_run_inr (pk : PK)
    (sk : SK) (msg : M)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    (progGameRunImplCombinedTrap psf M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let v ← ($ᵗ Range : ProbComp Range)
        let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
        pure ((r, x),
          (((s.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.2),
            s.1.2 || saltKeyed M Salt s.1.1.1 r),
            fun t' => if t' = (r, msg) then some x else s.2 t'))) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step distributional equality of the combined handler and its trapdoor-recording sibling.**
For every query `t` and every state `s`, the combined handler `progGameRunImplCombined` and the
trapdoor-recording handler `progGameRunImplCombinedTrap` produce *equal output distributions* on the
same state `s`, under GPV regularity `hreg` at `(pk, sk)`.

On a uniform query and on a random-oracle cache *hit* the two handlers are literally identical.  On
a programming step (random-oracle miss or signing) the only difference is the joint law of the
`(cached image, recorded preimage)` pair drawn at that step: `(psf.eval pk sd, sd)` for
`sd ← domainSample pk` on the combined side, versus `(v, x)` for `v ← $ᵗ Range`,
`x ← trapdoorSample pk sk v` on the trapdoor side — the two sides of `hreg`.  Mapping `hreg` through
the (deterministic) cache/table update yields the per-step equality.  This is the local hypothesis
of `evalDist_simulateQ_run_eq_of_impl_evalDist_eq`. -/
lemma evalDist_progGameRunImplCombined_step_eq_trap
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    𝒟[(progGameRunImplCombined psf M Salt domainSample pk t).run s] =
      𝒟[(progGameRunImplCombinedTrap psf M Salt pk sk t).run s] := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl, progGameRunImplCombinedTrap_run_inl_inl]
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr, progGameRunImplCombinedTrap_run_inl_inr]
          cases hq : s.1.1.1 q with
          | some v => rfl
          | none =>
              -- Programming step (miss): map `hreg` through the cache/table update keyed at `q`.
              have h := congrArg (Functor.map
                (fun p : Range × Domain =>
                  (p.1,
                    (((s.1.1.1.cacheQuery q p.1, s.1.1.2), s.1.2),
                      fun t' => if t' = q then some p.2 else s.2 t'))
                    : Range × Domain →
                      Range × ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
                        ((Salt × M) → Option Domain)))) hreg
              simpa only [← evalDist_map, map_bind, map_pure, bind_assoc] using h
  | inr msg =>
      rw [progGameRunImplCombined_run_inr, progGameRunImplCombinedTrap_run_inr]
      -- Programming step (signing): draw salt `r`, then map `hreg` through the salt-keyed update.
      refine evalDist_bind_congr fun r _ => ?_
      have h := congrArg (Functor.map
        (fun p : Range × Domain =>
          ((r, p.2),
            (((s.1.1.1.cacheQuery (r, msg) p.1, insert msg s.1.1.2),
              s.1.2 || saltKeyed M Salt s.1.1.1 r),
              fun t' => if t' = (r, msg) then some p.2 else s.2 t'))
            : Range × Domain →
              (Salt × Domain) × ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
                ((Salt × M) → Option Domain)))) hreg
      simpa only [← evalDist_map, map_bind, map_pure, bind_assoc] using h

omit [DecidableEq Range] [Fintype Salt] in
/-- **Lemma A — write-only-table deferral / `eval→trapdoor-recording` run rewrite.** For *any*
adaptive computation `oa` and any start state `s`, the full simulated run of the combined handler
`progGameRunImplCombined` over `oa` is *equidistributed* with the run of the trapdoor-recording
handler `progGameRunImplCombinedTrap`, under GPV regularity `hreg` at `(pk, sk)`.

The two handlers agree query-by-query as output distributions on the same state
(`evalDist_progGameRunImplCombined_step_eq_trap`); the distributional simulation engine
`evalDist_simulateQ_run_eq_of_impl_evalDist_eq` threads that per-step equality through the entire
adaptive fold as an exact equidistribution.  No pointwise relation between the two runs' successor
states is required: the only per-step difference is the *joint* law of the
`(cached image, recorded preimage)` pair, which `hreg` equates target-by-target — and because the
recorded preimage is never read during the run (the table is write-only), this purely local
substitution suffices.  This is the structural collapse of the GPV Step-2 reservoir coupling: the
recorded preimage `sd⋆` is re-expressed, run-for-run, as the trapdoor preimage `x⋆` of the cached
image, matching the reservoir reduction's challenger preimage of the embedded uniform target. -/
lemma evalDist_run_progGameRunImplCombinedTrap_eq {β : Type}
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    𝒟[(simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s] =
      𝒟[(simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk) oa).run s] :=
  evalDist_simulateQ_run_eq_of_impl_evalDist_eq
    (progGameRunImplCombined psf M Salt domainSample pk)
    (progGameRunImplCombinedTrap psf M Salt pk sk)
    (evalDist_progGameRunImplCombined_step_eq_trap psf M Salt domainSample pk sk hreg) oa s

/-! #### D3. Projection of the combined handler onto the collision-reduction handler

Dropping the signed-set and the collision flag (`proj = fun s => (s.1.1.1, s.2)`, keeping the cache
and the hidden table) from the combined handler recovers the collision reduction's internal handler
`reductionImpl`. The signed-set and flag are passive auxiliaries over the reduction's cache/table
state: both handlers draw the *same* preimage and update the cache and table identically, so
projecting the game-only bookkeeping away commutes with each step and hence with the whole
simulation. -/

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-query reduction projection of the combined handler.** Dropping the signed-set and the flag
(`fun s => (s.1.1.1, s.2)`, keeping the cache and the hidden table) from one
`progGameRunImplCombined` query step recovers the corresponding `reductionImpl` step. This is the
per-query hypothesis of the state-projection transport `map_run_simulateQ_eq_of_query_map_eq`. -/
lemma progGameRunImplCombined_proj_reduction (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prod.map id
        (fun s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
            ((Salt × M) → Option Domain) => (s.1.1.1, s.2)) <$>
        (progGameRunImplCombined psf M Salt domainSample pk t).run s =
      (reductionImpl psf M Salt domainSample pk t).run (s.1.1.1, s.2) := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl, reductionImpl_run_inl_inl]
          rfl
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr, reductionImpl_run_inl_inr]
          cases s.1.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => rfl
  | inr msg =>
      rw [progGameRunImplCombined_run_inr, reductionImpl_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Run-level reduction projection of the combined handler.** Dropping the signed-set and the flag
from the full simulated run of `progGameRunImplCombined` over `oa` recovers the run of the collision
reduction's internal handler `reductionImpl`. Transports the per-query
`progGameRunImplCombined_proj_reduction` through the whole computation via
`map_run_simulateQ_eq_of_query_map_eq`: the signed-set and flag are passive over the reduction's
cache/table state. -/
lemma map_run_progGameRunImplCombined_proj_reduction (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prod.map id
        (fun s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
            ((Salt × M) → Option Domain) => (s.1.1.1, s.2)) <$>
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s =
      (simulateQ (reductionImpl psf M Salt domainSample pk) oa).run (s.1.1.1, s.2) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (fun s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain) => (s.1.1.1, s.2))
    (progGameRunImplCombined_proj_reduction psf M Salt domainSample pk) oa s

/-! #### D4. Cache/table coherence invariant of the combined handler

The combined handler keeps the cache and the hidden table coherent: at every programmed point `t`,
if the table records a hidden preimage `d`, then the cache value at `t` is exactly `psf.eval pk d`.
This holds because every table write `t ↦ s` is performed in lockstep with the cache write
`t ↦ psf.eval pk s` from the *same* drawn preimage `s`; cache hits and uniform queries touch
neither. The invariant is the structural certificate that lets the distinct-collision transfer read
a genuine `psf.eval`-collision off any forged fresh point. -/

/-- **Cache/table coherence predicate.** At every programmed point, a recorded hidden preimage in
the table is a `psf.eval pk`-preimage of the cached random-oracle value there. -/
def combinedCacheTableInv (pk : PK)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prop :=
  ∀ t : Salt × M, ∀ d : Domain, s.2 t = some d → s.1.1.1 t = some (psf.eval pk d)

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-step preservation of cache/table coherence.** Each `progGameRunImplCombined` query step
preserves `combinedCacheTableInv`: a uniform query and a random-oracle cache hit leave cache and
table unchanged; a random-oracle miss and a signing step add a *matched* pair `t ↦ s` (table) and
`t ↦ psf.eval pk s` (cache) at the same point, preserving coherence everywhere. -/
lemma combinedCacheTableInv_step (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedCacheTableInv psf M Salt pk s) :
    ∀ y ∈ support ((progGameRunImplCombined psf M Salt domainSample pk t).run s),
      combinedCacheTableInv psf M Salt pk y.2 := by
  intro y hy
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl] at hy
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
          obtain ⟨v, _, hw⟩ := hy
          subst hw
          exact hs
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr] at hy
          cases hq : s.1.1.1 q with
          | some v =>
              rw [hq] at hy
              simp only [support_pure, Set.mem_singleton_iff] at hy
              subst hy
              exact hs
          | none =>
              rw [hq] at hy
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
              obtain ⟨sd, hsd, hw⟩ := hy
              subst hw
              intro t' d ht'
              dsimp only at ht' ⊢
              by_cases htq : t' = q
              · subst htq
                rw [if_pos rfl, Option.some_inj] at ht'
                subst ht'
                exact QueryCache.cacheQuery_self _ _ _
              · rw [if_neg htq] at ht'
                rw [QueryCache.cacheQuery_of_ne _ _ htq]
                exact hs t' d ht'
  | inr msg =>
      rw [progGameRunImplCombined_run_inr] at hy
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨r, _, sd, hsd, hw⟩ := hy
      subst hw
      intro t' d ht'
      dsimp only at ht' ⊢
      by_cases htq : t' = (r, msg)
      · subst htq
        rw [if_pos rfl, Option.some_inj] at ht'
        subst ht'
        exact QueryCache.cacheQuery_self _ _ _
      · rw [if_neg htq] at ht'
        rw [QueryCache.cacheQuery_of_ne _ _ htq]
        exact hs t' d ht'

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Cache/table coherence holds throughout the combined simulation.** Starting from any state
satisfying `combinedCacheTableInv` (in particular the empty start `((∅, ∅, false), fun _ => none)`,
where it holds vacuously), every final state in the support of the full combined run over `oa`
satisfies it. Transports `combinedCacheTableInv_step` through the whole simulation via
`simulateQ_run_preserves_inv_of_query`. -/
lemma progGameRunImplCombined_run_inv (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedCacheTableInv psf M Salt pk s) :
    ∀ y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s),
      combinedCacheTableInv psf M Salt pk y.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _
    (combinedCacheTableInv psf M Salt pk)
    (combinedCacheTableInv_step psf M Salt domainSample pk) oa s hs

/-- **Cache ⇒ table coherence predicate.** At every programmed point, a cached random-oracle value
is the `psf.eval pk`-image of a recorded hidden preimage in the table.  This is the direction the
distinct-collision transfer needs: a verifying forgery hits a *cached* point, and this invariant
exhibits the simulator's hidden preimage there. -/
def combinedCacheImpliesTableInv (pk : PK)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prop :=
  ∀ t : Salt × M, ∀ v : Range, s.1.1.1 t = some v → ∃ d : Domain, s.2 t = some d ∧ v = psf.eval pk d

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-step preservation of cache ⇒ table coherence.** Each combined query step preserves
`combinedCacheImpliesTableInv`: uniform queries and cache hits leave both components untouched,
while random-oracle misses and signing steps write a matched pair `t ↦ psf.eval pk s` (cache) and
`t ↦ s` (table) at the same point. -/
lemma combinedCacheImpliesTableInv_step (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedCacheImpliesTableInv psf M Salt pk s) :
    ∀ y ∈ support ((progGameRunImplCombined psf M Salt domainSample pk t).run s),
      combinedCacheImpliesTableInv psf M Salt pk y.2 := by
  intro y hy
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl] at hy
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
          obtain ⟨v, _, hw⟩ := hy
          subst hw
          exact hs
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr] at hy
          cases hq : s.1.1.1 q with
          | some v =>
              rw [hq] at hy
              simp only [support_pure, Set.mem_singleton_iff] at hy
              subst hy
              exact hs
          | none =>
              rw [hq] at hy
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
              obtain ⟨sd, _hsd, hw⟩ := hy
              subst hw
              intro t' v' ht'
              dsimp only at ht' ⊢
              by_cases htq : t' = q
              · subst htq
                rw [QueryCache.cacheQuery_self, Option.some_inj] at ht'
                exact ⟨sd, by rw [if_pos rfl], ht'.symm⟩
              · rw [QueryCache.cacheQuery_of_ne _ _ htq] at ht'
                obtain ⟨d, hd, hv⟩ := hs t' v' ht'
                exact ⟨d, by rw [if_neg htq]; exact hd, hv⟩
  | inr msg =>
      rw [progGameRunImplCombined_run_inr] at hy
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨r, _, sd, _hsd, hw⟩ := hy
      subst hw
      intro t' v' ht'
      dsimp only at ht' ⊢
      by_cases htq : t' = (r, msg)
      · subst htq
        rw [QueryCache.cacheQuery_self, Option.some_inj] at ht'
        exact ⟨sd, by rw [if_pos rfl], ht'.symm⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ htq] at ht'
        obtain ⟨d, hd, hv⟩ := hs t' v' ht'
        exact ⟨d, by rw [if_neg htq]; exact hd, hv⟩

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Cache ⇒ table coherence holds throughout the combined simulation.** Starting from any state
satisfying `combinedCacheImpliesTableInv` (in particular the empty start, vacuously), every final
state of the combined run over `oa` satisfies it. -/
lemma progGameRunImplCombined_run_cacheImpliesTable (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedCacheImpliesTableInv psf M Salt pk s) :
    ∀ y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s),
      combinedCacheImpliesTableInv psf M Salt pk y.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _
    (combinedCacheImpliesTableInv psf M Salt pk)
    (combinedCacheImpliesTableInv_step psf M Salt domainSample pk) oa s hs

/-- **Table values are drawn preimages.** Every hidden preimage recorded in the combined run's table
lies in the support of the forward sampler `domainSample pk`. Every table write `t ↦ sd` records a
freshly drawn `sd ← domainSample pk`, so it is in the sampler's support; uniform queries and cache
hits leave the table untouched. -/
def combinedTableInDomainInv (M Salt : Type) (domainSample : PK → ProbComp Domain) (pk : PK)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Prop :=
  ∀ t : Salt × M, ∀ d : Domain, s.2 t = some d → d ∈ support (domainSample pk)

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **Per-step preservation of `combinedTableInDomainInv`.** -/
lemma combinedTableInDomainInv_step (domainSample : PK → ProbComp Domain) (pk : PK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedTableInDomainInv M Salt domainSample pk s) :
    ∀ y ∈ support ((progGameRunImplCombined psf M Salt domainSample pk t).run s),
      combinedTableInDomainInv M Salt domainSample pk y.2 := by
  intro y hy
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombined_run_inl_inl] at hy
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
          obtain ⟨v, _, hw⟩ := hy
          subst hw
          exact hs
      | inr q =>
          rw [progGameRunImplCombined_run_inl_inr] at hy
          cases hq : s.1.1.1 q with
          | some v =>
              rw [hq] at hy
              simp only [support_pure, Set.mem_singleton_iff] at hy
              subst hy
              exact hs
          | none =>
              rw [hq] at hy
              simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
              obtain ⟨sd, hsd, hw⟩ := hy
              subst hw
              intro t' d ht'
              dsimp only at ht' ⊢
              by_cases htq : t' = q
              · subst htq
                rw [if_pos rfl, Option.some_inj] at ht'
                subst ht'
                exact hsd
              · rw [if_neg htq] at ht'
                exact hs t' d ht'
  | inr msg =>
      rw [progGameRunImplCombined_run_inr] at hy
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hy
      obtain ⟨r, _, sd, hsd, hw⟩ := hy
      subst hw
      intro t' d ht'
      dsimp only at ht' ⊢
      by_cases htq : t' = (r, msg)
      · subst htq
        rw [if_pos rfl, Option.some_inj] at ht'
        subst ht'
        exact hsd
      · rw [if_neg htq] at ht'
        exact hs t' d ht'

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **`combinedTableInDomainInv` holds throughout the combined simulation.** -/
lemma progGameRunImplCombined_run_tableInDomain (domainSample : PK → ProbComp Domain) (pk : PK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs : combinedTableInDomainInv M Salt domainSample pk s) :
    ∀ y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s),
      combinedTableInDomainInv M Salt domainSample pk y.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _
    (combinedTableInDomainInv M Salt domainSample pk)
    (combinedTableInDomainInv_step psf M Salt domainSample pk) oa s hs

/-! ### Cross-monad WriterT-log → signed-set reconstruction

The unforgeability experiment runs the adversary under the WriterT signing-log handler stack
`baseW + signingOracle pk sk` (logging each signing query) inside the runtime's
`withStateOracle randomOracle ∅` bundle, and its winning Bool reads the freshness mask
`!log.wasQueried msg` off the WriterT log.  The freshness vehicle `gpvRealImplFresh` instead
threads a `Finset M` signed-set through the random-oracle `StateT QueryCache ProbComp` surface.
The lemmas in this block reconstruct the WriterT log as that signed-set, identifying the two runs
across the WriterT/StateT monad divide.  The route mirrors the FiatShamir kernel inside
`FiatShamirWithAbort.probOutput_unforgeableExp_eq_hybridExpAtKey_real`: fuse the inner WriterT pass
with the outer cache simulation (`writerTMapBase`), replay the WriterT log into a `StateT (List M)`
input log (`appendInputLog`), flatten the nested `StateT` (`flattenStateT`), and project the
flattened handler onto `gpvRealImplFresh` with the signed-set reconstructed as the logged messages'
`toFinset`. -/

/-- **The fused real WriterT handler over the random-oracle cache.** The signing handler of the
unforgeability experiment, with the public/random-oracle base simulated by the runtime's
`withStateOracle` interpreter (`outerLift + randomOracle` over `StateT QueryCache ProbComp`).  This
is the GPV analogue of FiatShamir's fused `base.writerTMapBase implW`: it equals
`baseW + withLogging signBody`, where `signBody msg = gpvRealImpl … (Sum.inr msg)` is the real GPV
signing body run on the cache (`reconstructImplW_eq`). -/
noncomputable def gpvOuter :
    QueryImpl (unifSpec + (Salt × M →ₒ Range))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) +
    (randomOracle : QueryImpl (Salt × M →ₒ Range)
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))

omit [Fintype Salt] in
/-- **`gpvRealImpl` is `gpvOuter ∘ₛ realGameRunImplNoLog`.** Restates the definition of
`gpvRealImpl` in terms of the named base handler `gpvOuter`. -/
lemma gpvRealImpl_eq_compose (pk : PK) (sk : SK) :
    gpvRealImpl psf hr M Salt pk sk =
      (gpvOuter M Salt ∘ₛ realGameRunImplNoLog psf hr M Salt pk sk) := rfl

omit [Fintype Salt] in
/-- **The base (non-signing) step of `gpvRealImpl` is `gpvOuter`.** On a public/random-oracle
query `Sum.inl q`, the composed real handler re-emits the query through `realGameRunImplNoLog`
(`= query q`) and the `gpvOuter` simulation answers it, so `gpvRealImpl … (Sum.inl q) = gpvOuter q`.
-/
lemma gpvRealImpl_inl_eq_gpvOuter (pk : PK) (sk : SK)
    (q : (unifSpec + (Salt × M →ₒ Range)).Domain) :
    gpvRealImpl psf hr M Salt pk sk (Sum.inl q) = gpvOuter M Salt q := by
  simp only [gpvRealImpl_eq_compose, QueryImpl.compose, realGameRunImplNoLog, HAdd.hAdd,
    QueryImpl.add, HasQuery.toQueryImpl_apply, HasQuery.query]
  exact simulateQ_spec_query (gpvOuter M Salt) q

open Classical in
omit [Fintype Salt] in
/-- **Handler fusion: the fused WriterT stack is `baseW + withLogging signBody`.** Pushing the
runtime's `withStateOracle` interpreter `gpvOuter` through the base monad of the unforgeability
experiment's WriterT handler stack `baseW + signingOracle pk sk` (via `writerTMapBase`) yields the
WriterT handler `baseW' + withLogging signBody` over `StateT QueryCache ProbComp`, where the
public/random-oracle base re-emits its query through the cache (`baseW'`) and the signing body is
the real GPV signing computation run on the cache (`signBody msg = gpvRealImpl … (Sum.inr msg)`).
This is the GPV analogue of the FiatShamir `hHandler` step. -/
lemma gpvOuter_writerTMapBase_implW (pk : PK) (sk : SK) :
    (gpvOuter M Salt).writerTMapBase
        ((HasQuery.toQueryImpl (spec := unifSpec + (Salt × M →ₒ Range))
          (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).signingOracle pk sk) =
      (gpvOuter M Salt).liftTarget
          (WriterT (QueryLog (M →ₒ (Salt × Domain)))
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) +
        QueryImpl.withLogging
          (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg) :
            QueryImpl (M →ₒ (Salt × Domain))
              (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) := by
  funext t
  rcases t with bq | sq
  · -- public/random-oracle base query: `writerTMapBase` runs the lifted query through `gpvOuter`.
    ext s
    simp only [QueryImpl.writerTMapBase, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.toHasQuery_query, WriterT.mk, HasQuery.toQueryImpl_apply]
    rfl
  · -- signing query: `signingOracle = withLogging sign`; `(withLogging sign sq).run = sign sq >>=
    -- fun u => (u, [⟨sq, u⟩])` re-emits the log, so the fused LHS commutes the monad-morphism
    -- `simulateQ gpvOuter` through that base bind, and the RHS `withLogging` of `gpvRealImpl`
    -- (`= simulateQ gpvOuter ∘ sign` by the `∘ₛ` definition) is the same bind.
    ext s
    -- `gpvRealImpl … (Sum.inr msg) = simulateQ gpvOuter ((GPVHashAndSign …).sign pk sk msg)` holds
    -- definitionally (the `∘ₛ` definition), so expanding both `withLogging` bodies and commuting
    -- the monad-morphism `simulateQ gpvOuter` through the `sign >>= fun u => (u, [⟨sq, u⟩])` bind
    -- aligns the two runs.  Mirrors the FiatShamir `fsBaseImpl_writerTMapBase_signingOracle_eq`
    -- signing case.
    simp [QueryImpl.writerTMapBase, SignatureAlg.signingOracle, QueryImpl.withLogging_apply,
      GPVHashAndSign, gpvRealImpl, gpvOuter, QueryImpl.compose, realGameRunImplNoLog,
      QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_pure,
      simulateQ_bind, simulateQ_pure, WriterT.run_bind, WriterT.run_liftM,
      WriterT.run_tell, WriterT.run_pure, map_eq_bind_pure_comp]
    simp only [HAdd.hAdd, QueryImpl.add, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind, Function.comp_def]

omit [Fintype Salt] in
/-- **Per-query state-projection of the flattened append-log handler onto `gpvRealImplFresh`.**
The flattened `StateT (List M × QueryCache)` handler — the lifted public/random-oracle base plus the
`appendInputLog`-instrumented GPV signing body `gpvRealImpl … (Sum.inr ·)` — projects, under
`proj (l, c) = (c, l.toFinset)`, onto the freshness vehicle `gpvRealImplFresh` step by step.  On a
non-signing query both leave the signed-set untouched and evolve the cache through `gpvRealImpl`; on
a signing query `appendInputLog` appends `msg` to the list (`l ++ [msg]`) while `gpvRealImplFresh`
inserts it into the signed-set, reconciled by `(l ++ [msg]).toFinset = insert msg l.toFinset` (the
list-order is invisible to the `Finset`).  This is the per-query hypothesis of the state-projection
transport `map_run_simulateQ_eq_of_query_map_eq`, the GPV analogue of the FiatShamir `hmatch`. -/
lemma flattenAppendLog_proj_gpvRealImplFresh (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : List M × (Salt × M →ₒ Range).QueryCache) :
    Prod.map id (fun s : List M × (Salt × M →ₒ Range).QueryCache => (s.2, s.1.toFinset)) <$>
        ((((gpvOuter M Salt).liftTarget
              (StateT (List M) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))) +
            QueryImpl.appendInputLog
              (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg) :
                QueryImpl (M →ₒ (Salt × Domain))
                  (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))).flattenStateT t).run s =
      (gpvRealImplFresh psf hr M Salt pk sk t).run (s.2, s.1.toFinset) := by
  obtain ⟨l, c⟩ := s
  cases t with
  | inl q =>
      -- public/random-oracle base query: the list is untouched, the cache evolves through
      -- `gpvRealImpl`; both sides drop to the same base step `gpvOuter q = gpvRealImpl … (inl q)`.
      rw [gpvRealImplFresh_run_inl, gpvRealImpl_inl_eq_gpvOuter]
      simp only [QueryImpl.flattenStateT, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        StateT.run_mk, Prod.map, id_eq, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_def]
      -- `(liftM (gpvOuter q)).run l = gpvOuter q >>= fun a => (a, l)` is definitional; rephrase the
      -- nested lifted run so the cache run distributes and the list rides through unchanged.
      change ((gpvOuter M Salt q >>= fun a => pure (a, l)).run c >>= fun x =>
          pure (x.1.1, x.2, x.1.2.toFinset)) = _
      rw [StateT.run_bind]
      simp only [StateT.run_pure, bind_assoc, pure_bind]
      rfl
  | inr msg =>
      -- signing query: `appendInputLog` appends `msg` to the list, `gpvRealImplFresh` inserts it
      -- into the signed-set, reconciled by `(l ++ [msg]).toFinset = insert msg l.toFinset`.
      rw [gpvRealImplFresh_run_inr]
      simp only [QueryImpl.flattenStateT, QueryImpl.add_apply_inr, QueryImpl.appendInputLog_apply,
        StateT.run_mk, Prod.map, id_eq, map_bind, map_pure]
      -- `(modify (· ++ [msg]) >>= liftM (gpvRealImpl …)).run l = gpvRealImpl … >>= fun a => (a,
      -- l ++ [msg])` is definitional; then `gpvRealImpl_run_sign` exposes the explicit sign body
      -- and `(l ++ [msg]).toFinset = insert msg l.toFinset` reconciles the signed-set.
      change ((gpvRealImpl psf hr M Salt pk sk (Sum.inr msg) >>=
            fun a => pure (a, l ++ [msg])).run c
          >>= fun a => pure (a.1.1, a.2, a.1.2.toFinset)) = _
      rw [StateT.run_bind, gpvRealImpl_run_sign]
      simp only [StateT.run_pure, bind_assoc, pure_bind,
        show (l ++ [msg]).toFinset = insert msg l.toFinset by simp [List.toFinset_append]]

omit [Fintype Salt] in
/-- **Cross-monad WriterT-log → signed-set run reconstruction.** Running `oa` under the
unforgeability experiment's WriterT signing-log handler stack `baseW + signingOracle pk sk`, then
interpreting its base random-oracle queries through the runtime's `withStateOracle` cache
(`gpvOuter`) and mapping the result to `(output, (log.map fst).toFinset, cache)`, coincides with the
freshness vehicle `gpvRealImplFresh` run started from `(∅, ∅), false`, projected to drop the passive
collision flag.

This is the kernel of the freshness game-identification (N)(a): it identifies the WriterT signing
log of `unforgeableExp` with the `Finset M` signed-set carried by `gpvRealImplFresh`, across the
WriterT/StateT monad divide.  The proof chains the reconstruction pieces, mirroring the
FiatShamir `probOutput_unforgeableExp_eq_hybridExpAtKey_real` kernel:
`simulateQ_writerTMapBase_run` + `gpvOuter_writerTMapBase_implW` (fuse the inner WriterT pass with
the outer cache simulation into `baseW' + withLogging signBody`),
`map_run_withLogging_inputs_eq_run_appendInputLog` (replay the WriterT log into a `StateT (List M)`
input log, `initialInputs = []`), `simulateQ_flattenStateT_run` (flatten the nested `StateT`), and
`flattenAppendLog_proj_gpvRealImplFresh` via `map_run_simulateQ_eq_of_query_map_eq` (project onto
`gpvRealImplFresh`, the signed-set reconstructed as the logged messages' `toFinset`). -/
lemma map_simulateQ_gpvOuter_writerLog_eq_gpvRealImplFresh (pk : PK) (sk : SK) {β : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    (fun z : (β × QueryLog (M →ₒ (Salt × Domain))) × (Salt × M →ₒ Range).QueryCache =>
        (z.1.1, z.2, (z.1.2.map (fun e => e.1)).toFinset)) <$>
        (simulateQ (gpvOuter M Salt)
          ((simulateQ
              ((HasQuery.toQueryImpl (spec := unifSpec + (Salt × M →ₒ Range))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                  (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                    (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
                (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                  psf hr M Salt).signingOracle pk sk)
              oa).run)).run (∅ : (Salt × M →ₒ Range).QueryCache)
      = (fun z : β × ((Salt × M →ₒ Range).QueryCache × Finset M) =>
          (z.1, z.2.1, z.2.2)) <$>
        (simulateQ (gpvRealImplFresh psf hr M Salt pk sk) oa).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)) := by
  classical
  -- The fused base `gpvOuter.liftTarget (WriterT …)` is `(HasQuery.toQueryImpl).liftTarget` for the
  -- `HasQuery` instance `gpvOuter.toHasQuery`; provide it so the replay lemma's `baseW` matches.
  letI hq : HasQuery (unifSpec + (Salt × M →ₒ Range))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) := (gpvOuter M Salt).toHasQuery
  -- (1) Fuse the inner WriterT pass with the outer cache simulation `gpvOuter` via
  -- `writerTMapBase`, and rewrite the fused handler as `baseW' + withLogging signBody`.
  rw [QueryImpl.simulateQ_writerTMapBase_run, gpvOuter_writerTMapBase_implW]
  -- (2) Replay the WriterT log into a `StateT (List M)` input log starting from `[]`.
  have hreplay := QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
    (spec₀ := unifSpec + (Salt × M →ₒ Range)) (loggedSpec := M →ₒ (Salt × Domain))
    (m₀ := StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)
    (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg)) oa ([] : List M)
  simp only [List.nil_append] at hreplay
  -- Apply the run, flatten the nested `StateT (List M) (StateT cache)`, and project to
  -- `gpvRealImplFresh` via the per-query `hmatch`.
  have hflatten := OracleComp.simulateQ_flattenStateT_run
    ((gpvOuter M Salt).liftTarget
        (StateT (List M) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) +
      QueryImpl.appendInputLog
        (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg) :
          QueryImpl (M →ₒ (Salt × Domain))
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
    oa ([] : List M) (∅ : (Salt × M →ₒ Range).QueryCache)
  have hflat := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (((gpvOuter M Salt).liftTarget
        (StateT (List M) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) +
      QueryImpl.appendInputLog
        (fun msg => gpvRealImpl psf hr M Salt pk sk (Sum.inr msg) :
          QueryImpl (M →ₒ (Salt × Domain))
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp))).flattenStateT)
    (gpvRealImplFresh psf hr M Salt pk sk)
    (fun s : List M × (Salt × M →ₒ Range).QueryCache => (s.2, s.1.toFinset))
    (flattenAppendLog_proj_gpvRealImplFresh psf hr M Salt pk sk) oa
    (([], ∅) : List M × (Salt × M →ₒ Range).QueryCache)
  -- Rewrite the RHS `gpvRealImplFresh` run via `hflat` (the state-projection of the flattened
  -- append-log run), then `hflatten` (flatten = nested run) and `hreplay` (WriterT log → input
  -- list), reducing both sides to the same base computation; the three maps compose pointwise.
  simp only [List.toFinset_nil] at hflat
  rw [← hflat, Functor.map_map, hflatten]
  -- The fused base `HasQuery.toQueryImpl` (for the instance `hq := gpvOuter.toHasQuery`) is exactly
  -- `gpvOuter`, so the replay lemma's base matches the flattened run's base.
  have hbase : (@HasQuery.toQueryImpl _ (unifSpec + (Salt × M →ₒ Range))
      (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) hq) = gpvOuter M Salt := rfl
  -- The flattened nested run (RHS, via `hflat`/`hflatten`) and the replayed WriterT-log input-list
  -- run (`hreplay`, applied at the cache `∅`) are the same base computation; the maps compose.
  have hreplay' := congrArg
    (fun (g : StateT ((Salt × M →ₒ Range).QueryCache) ProbComp _) => g.run ∅) hreplay
  simp only [StateT.run_map, hbase] at hreplay'
  rw [← hreplay']
  simp only [bind_pure_comp, Functor.map_map, Prod.map, id_eq]

/-! ### Verify-Bool games on the freshness-tracking vehicle

The verification read `gpvVerifyRead` recomputes the random-oracle value at the forged `(r, msg)`
and checks `eval pk s = c ∧ isShort s` — the GPV `verify` body, phrased over the sum spec as a
single random-oracle query (zero signing queries).  Appended after `adv.main pk` on the
freshness-tracking vehicle, it reads against the *shared* random-oracle cache (so a forgery on a
cached programmed point is observed) and the resulting state still carries the signed-set, so the
winning Bool can apply the EUF-CMA freshness mask (the forged message not being among the signed
messages).  These are the two
`SPMF Bool` games the fresh verify-Bool coupling `gpv_tvDist_orig_verify_fresh_le_collisionBound`
relates within `collisionBound`. -/

/-- **GPV verification read (sum-spec, signing-free).** On a forgery `out = (msg, (r, s))`, query
the random oracle at `(r, msg)` and return `eval pk s = c ∧ isShort s` — the `verify` body of the
GPV scheme phrased as a single random-oracle query into the sum spec.  It issues exactly one
random-oracle query and *no* signing query, so it is a valid signing-free continuation for the
verify-Bool coupling. -/
def gpvVerifyRead (pk : PK) (out : M × (Salt × Domain)) :
    OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) Bool :=
  let (msg, (r, s)) := out
  (liftM (((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).query
      (Sum.inl (Sum.inr (r, msg)))) : OracleComp _ Range) >>= fun c =>
    pure (decide (psf.eval pk s = c) && psf.isShort s)

omit [SampleableType Range] [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]
  [Fintype Salt] in
/-- **`gpvVerifyRead` is signing-free.** The verification read issues a single random-oracle query
(an `.inl (.inr _)` index) and no signing query, so it satisfies the signing-free query bound
`IsQueryBoundP (· matches .inr _) 0` required by the verify-Bool coupling. -/
lemma gpvVerifyRead_no_sign (pk : PK) (out : M × (Salt × Domain)) :
    (gpvVerifyRead psf M Salt pk out).IsQueryBoundP (· matches .inr _) 0 := by
  obtain ⟨msg, r, s⟩ := out
  simp only [gpvVerifyRead, bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
  refine (OracleComp.isQueryBoundP_query_iff _ (Sum.inl (Sum.inr (r, msg))) 0).mpr (fun h => ?_)
  simp at h

open Classical in
/-- **Real verify-Bool game on the freshness-tracking vehicle.** The adversary's main computation
followed by the verification read, simulated on the *real* fresh flag handler from the empty cache,
empty signed-set, and unset flag; the winning Bool combines the verification result `z.1.2` with the
EUF-CMA freshness mask `z.1.1.1 ∉ z.2.1.2` (the forged message is not among the signed messages). -/
noncomputable def realGameVerifyFresh
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (pk : PK) (sk : SK) : SPMF Bool :=
  𝒟[(fun z : ((M × (Salt × Domain)) × Bool) ×
        (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) =>
        decide (z.1.1.1 ∉ z.2.1.2) && z.1.2) <$>
      (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk)
        (adv.main pk >>= fun out =>
          (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)]

open Classical in
/-- **Programmed verify-Bool game on the freshness-tracking vehicle.** The programmed dual of
`realGameVerifyFresh`: the same adversary-plus-verification computation simulated on the
*programmed* fresh flag handler. -/
noncomputable def progGameVerifyFresh
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (pk : PK) : SPMF Bool :=
  𝒟[(fun z : ((M × (Salt × Domain)) × Bool) ×
        (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) =>
        decide (z.1.1.1 ∉ z.2.1.2) && z.1.2) <$>
      (simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
        (adv.main pk >>= fun out =>
          (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)]

omit [SampleableType Range] [DecidableEq M] [DecidableEq Salt] [SampleableType Salt]
  [Fintype Salt] in
/-- **The verification continuation is signing-free.** The freshness-game continuation
`fun out => (out, ·) <$> gpvVerifyRead pk out` issues exactly one random-oracle read (inside
`gpvVerifyRead`) and *no* signing query, so it meets the signing-free query bound
`IsQueryBoundP (· matches .inr _) 0` required by the fresh verify-Bool coupling. -/
lemma gpvVerifyKont_no_sign (pk : PK) (out : M × (Salt × Domain)) :
    ((fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out).IsQueryBoundP
      (· matches .inr _) 0 := by
  rw [OracleComp.isQueryBoundP_map_iff]
  exact gpvVerifyRead_no_sign psf M Salt pk out

/-- **Freshness-mask reconstruction bridge.** The EUF-CMA freshness check
`!log.wasQueried msg`, reading the WriterT signing log, equals the freshness predicate
`decide (msg ∉ (log.map fst).toFinset)` reading the signed-set reconstructed from the log: the
message is fresh iff it is not among the logged signing inputs. This is the pointwise identity that
lets the WriterT-log-keyed mask of the unforgeability experiment be read off the `Finset M`
signed-set carried by `gpvRealImplFlagFresh`. -/
lemma not_wasQueried_eq_decide_not_mem_toFinset {κ : Type} {spec : OracleSpec κ}
    [spec.DecidableEq] (log : QueryLog spec) (t : spec.Domain) :
    (!log.wasQueried t) = decide (t ∉ (log.map (fun e => e.1)).toFinset) := by
  rw [QueryLog.wasQueried_eq_decide_mem_map_fst]
  simp only [List.mem_toFinset, decide_not]

/-- **Coupling hop (b) on the freshness-tracking verify-Bool games.** The real freshness verify-Bool
game's success probability is bounded by the programmed one plus `collisionBound`.

This is the bool-valued, data-processed shadow of the fresh verify-Bool coupling
`gpv_tvDist_orig_verify_fresh_le_collisionBound`: both `realGameVerifyFresh` and
`progGameVerifyFresh` are the *same* `decide (·.1.1.1 ∉ ·.2.1.2) && ·.1.2`-map of the two
vehicle runs of `adv.main pk >>= verify` on the real / programmed fresh flag handlers, so the
total-variation contraction `tvDist_map_le` reduces their bool TV to the run-level TV, which the
fresh coupling (with the signing-free verification continuation, `gpvVerifyKont_no_sign`)
bounds by `(collisionBound …).toReal`.  Transporting through the bool-valued bridge
`abs_probOutput_toReal_sub_le_tvDist` gives the `ℝ≥0∞` inequality. -/
theorem gpv_realGameVerifyFresh_le_progGameVerifyFresh_add_collisionBound
    [Finite Range] [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    Pr[= true | realGameVerifyFresh psf hr M Salt adv pk sk]
      ≤ Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pk]
        + collisionBound Salt qSign qHash := by
  classical
  have hcb_lt_top : collisionBound Salt qSign qHash < ⊤ := by
    refine ENNReal.div_lt_top ?_ ?_
    · simp
    · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
      exact Fintype.card_ne_zero
  -- The two games are the same `decide (·) && ·`-map of the two vehicle runs; `tvDist_map_le`
  -- reduces their bool TV to the run-level TV bounded by the fresh coupling.
  let f : ((M × (Salt × Domain)) × Bool) ×
        (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) → Bool :=
    fun z => decide (z.1.1.1 ∉ z.2.1.2) && z.1.2
  let kont : M × (Salt × Domain) →
      OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        ((M × (Salt × Domain)) × Bool) :=
    fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out
  let runReal := (simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) (adv.main pk >>= kont)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)
  let runProg := (simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
        (adv.main pk >>= kont)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)
  have hgoal : Pr[= true | realGameVerifyFresh psf hr M Salt adv pk sk]
      = Pr[= true | f <$> runReal] := rfl
  have hgoalProg : Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pk]
      = Pr[= true | f <$> runProg] := rfl
  rw [hgoal, hgoalProg]
  rw [← ENNReal.ofReal_toReal probOutput_ne_top,
      ← ENNReal.ofReal_toReal (a := Pr[= true | f <$> runProg]) probOutput_ne_top,
      ← ENNReal.ofReal_toReal hcb_lt_top.ne,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbridge := abs_probOutput_toReal_sub_le_tvDist (f <$> runReal) (f <$> runProg)
  have hsub := (abs_le.mp hbridge).2
  have hmap : tvDist (f <$> runReal) (f <$> runProg) ≤ tvDist runReal runProg :=
    tvDist_map_le f runReal runProg
  have hcouple : tvDist runReal runProg ≤ (collisionBound Salt qSign qHash).toReal :=
    gpv_tvDist_orig_verify_fresh_le_collisionBound psf hr M Salt pk sk adv domainSample kont
      qSign qHash hQ (gpvVerifyKont_no_sign psf M Salt pk) hNF hreg
  linarith [le_trans hsub (le_trans hmap hcouple)]

omit [DecidableEq Range] [SampleableType Range] [DecidableEq M] [DecidableEq Salt]
  [SampleableType Salt] [Fintype Salt] in
/-- **Lifted public-randomness run under the bundled state base.** Simulating a lifted
public-randomness `ProbComp` `oa` under the bundled identity base
`(QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp)` runs `oa` verbatim, pairing
each output with the unchanged state `s`. The hidden state is inert for public-randomness queries.
This is the bundled-base analogue of `unifFwdImpl.simulateQ_run` for a general state type `σ`. -/
theorem simulateQ_ofLift_liftTarget_run {σ : Type} {α : Type} (oa : ProbComp α) (s : σ) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp))
      (oa : OracleComp unifSpec α)).run s = (fun x => (x, s)) <$> oa := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have hlift : (liftM (liftM (OracleSpec.query t) : ProbComp (unifSpec.Range t)) :
        StateT σ ProbComp (unifSpec.Range t)).run s
        = (fun x => (x, s)) <$> (liftM (OracleSpec.query t) : ProbComp (unifSpec.Range t)) := by
      rw [StateT.run_monadLift]; rfl
    rw [hlift, map_eq_bind_pure_comp, bind_assoc]
    simp only [pure_bind, Function.comp_def]
    rw [show (liftM (OracleSpec.query t) : ProbComp (unifSpec.Range t)) >>= oa
        = liftM (OracleSpec.query t) >>= oa from rfl]
    rw [map_eq_bind_pure_comp, bind_assoc]
    refine bind_congr fun u => ?_
    rw [ih u]
    simp [map_eq_bind_pure_comp]

/-- **Keygen-averaging peel for the bundled `withStateOracle` semantics (reconstruction piece of the
game-identification (N)(a)).** A surface computation that begins by lifting a public-randomness
`ProbComp` prefix `oa` (e.g. the GPV key generation `liftM hr.gen`) into the oracle world and then
continues with `rest` factors, under the bundled `withStateOracle hashImpl ∅` `SPMF` semantics, as
the `SPMF`-average over `𝒟[oa]` of the semantics of the continuation.

The public-randomness prefix touches neither the random-oracle cache nor the hidden state: it is
simulated by the lifted identity implementation (`QueryImpl.simulateQ_add_liftComp_left` drops the
`hashImpl` summand on the lifted sub-computation, `unifFwdImpl.simulateQ_run` runs it as
`(·, ∅) <$> oa`), so its draws commute straight out of the bundle. This is the GPV-runtime keygen
peel of the game-identification (N)(a) — the analogue of the FiatShamir
`roSim.run'_liftM_bind`-style averaging step that opens
`probOutput_unforgeableExp_eq_hybridExpAtKey_real`. -/
theorem withStateOracle_evalDist_liftM_bind {ι : Type} {hashSpec : OracleSpec ι}
    (hashImpl : QueryImpl hashSpec (StateT hashSpec.QueryCache ProbComp))
    {α β : Type} (oa : ProbComp α)
    (rest : α → OracleComp (unifSpec + hashSpec) β) :
    (SPMFSemantics.withStateOracle hashImpl ∅).evalDist (liftM oa >>= rest)
      = (𝒟[oa] : SPMF α) >>= fun x =>
          (SPMFSemantics.withStateOracle hashImpl ∅).evalDist (rest x) := by
  classical
  unfold SPMFSemantics.evalDist SPMFSemantics.withStateOracle
  simp only [SemanticsVia.denote]
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  rw [show simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT hashSpec.QueryCache ProbComp) + hashImpl) (liftM oa)
      = simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT hashSpec.QueryCache ProbComp)) oa
      from QueryImpl.simulateQ_add_liftComp_left _ hashImpl oa]
  rw [simulateQ_ofLift_liftTarget_run oa ∅, map_bind, bind_map_left, liftM_bind]
  rfl

/-- **Step 1 (sign-then-hash ≡ real) TV bound, over the pinned GPV game runs.**

This is the salt-inclusive sign-then-hash hop *over the pinned GPV game runs*, with the run-level
coupling supplied by the original-run cardinality telescope `(A2)`
`gpv_orig_flag_le_collisionBound`.
The real run `realGameRun … adv pk sk` (the real EUF-CMA game) and the programmed run
`progGameRun … adv domainSample pk` (the randomized sign-then-hash game of the collision reduction)
are the two distributions of the sign-then-hash hop; given the query bound `hQ`, the trapdoor
totality `hNF`, and PSF regularity `hreg`, their total-variation distance is bounded by
`(collisionBound Salt qSign qHash).toReal`.

It is the GPV instance of the U2 surface
`tvDist_runtime_real_programmed_le_collisionBound_saltInclusive`, but unconditional and over the
actual game run.

**Proof route (original-run, inline salt).** The proof chains the identical-until-bad
reduction `gpv_tvDist_orig_run_le_probEvent_flag` — which bounds the Step-1 TV directly by the
run-level collision-flag probability of the flag-instrumented *original* (inline-salt) real handler
`gpvRealImplFlag` (consuming the universal off-bad agreement `gpvImplFlag_h_agree_good` and the
bad-monotonicity `h_mono`s) — with the original-run cardinality telescope `(A2)`
`gpv_orig_flag_le_collisionBound`, which bounds that flag probability by
`(collisionBound …).toReal`.  Because each signing salt is drawn inline at its step, this route
avoids the upfront-tape re-interleaving that the front-tape coupling
`gpv_tvDist_tape_runs_le_collisionBound` `(A)` requires. -/
theorem gpv_tvDist_real_programmed_le_collisionBound
    [Finite Range] [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))]) :
    SPMF.tvDist (realGameRun psf hr M Salt adv pk sk)
        (progGameRun psf hr M Salt adv domainSample pk)
      ≤ (collisionBound Salt qSign qHash).toReal := by
  classical
  -- Original-run route: the identical-until-bad reduction bounds the Step-1 TV by the
  -- run-level collision-flag probability of the inline-salt flag handler
  -- (`gpv_tvDist_orig_run_le_probEvent_flag`), which the original-run cardinality telescope `(A2)`
  -- `gpv_orig_flag_le_collisionBound` bounds by `(collisionBound …).toReal`.
  refine le_trans
    (gpv_tvDist_orig_run_le_probEvent_flag psf hr M Salt pk sk adv domainSample hNF hreg) ?_
  exact gpv_orig_flag_le_collisionBound psf hr M Salt pk sk adv qSign qHash hQ

/-! ## State-threading bridge: runtime ↦ bare random oracle

The GPV `runtime` interprets the surface program over the *sum* spec
`unifSpec + (Salt × M →ₒ Range)` via
`simulateQ' ((QueryImpl.ofLift unifSpec ProbComp).liftTarget _ + randomOracle)`. The reusable
state-threading bridge in `ProgramLogic/Relational/ProgrammingOracle.lean`
(`tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad`) is instead stated for the bare
single-spec lazy random oracle `simulateQ randomOracle`. The lemma
`runtime_evalDist_liftComp` is the missing reduction connecting the two: on a sub-computation that
only touches the random oracle (a hash-only `OracleComp (Salt × M →ₒ Range)` lifted into the sum),
the runtime's bundled `SPMF` semantics collapse to the bare `randomOracle` run from the empty
cache. -/

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **Pre-bridge.** On a random-oracle-only sub-computation `ob` lifted into the sum spec, the GPV
runtime's `SPMF` semantics equal the externally observed bare lazy random-oracle run from the empty
cache.

This is the reduction from the runtime's sum-spec `simulateQ'` interpreter down to the bare
`simulateQ randomOracle` form expected by the random-oracle state-threading bridge. It is
proved by unfolding `withStateOracle` and applying `QueryImpl.simulateQ_add_liftComp_right`, which
discards the (lifted-identity) uniform-sampling handler on a computation that never queries it. -/
theorem runtime_evalDist_liftComp {α : Type} (ob : OracleComp (Salt × M →ₒ Range) α) :
    (runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range)))
      = (liftM (StateT.run'
          (simulateQ (randomOracle :
            QueryImpl (Salt × M →ₒ Range) (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ob)
          ∅) : SPMF α) := by
  classical
  unfold ProbCompRuntime.evalDist runtime
  change (SPMFSemantics.withStateOracle _ ∅).evalDist _ = _
  unfold SPMFSemantics.evalDist SPMFSemantics.withStateOracle
  simp only [SemanticsVia.denote]
  rw [QueryImpl.simulateQ_add_liftComp_right]

/-! ## U2: sign-then-hash ≡ real, up to the programming bad event

The "sign-then-hash ≡ real" hop replaces the real lazy random oracle by a `policy`-programmed one
(the simulator programs each fresh signing target with `psf.eval pk s` for a freshly sampled short
preimage `s`). This is **not** an exact distributional equality: it is exact up to the
*programming bad event*, namely that a freshly sampled signing salt collides with an entry already
present in the random-oracle cache. `tvDist_runtime_real_programmed_le_bad` is the exact
core of the hop: the total-variation distance between the real-runtime output and the
programmed-run output is bounded by the probability that the programming bad flag fires.

The `Fintype Range`/`Inhabited Range` hypotheses supply the `IsUniformSpec (Salt × M →ₒ Range)`
instance required by the state-threading bridge; they are mild for a hash range. -/

omit [DecidableEq Range] [SampleableType Salt] [Fintype Salt] in
/-- **U2 core: sign-then-hash up-to-bad TV bound.**

For any random-oracle-only sub-computation `ob` and any programming `policy`, the total-variation
distance between the *real* GPV runtime output and the *programmed* (sign-then-hash) output is
bounded by the probability that the programming bad flag fires during the programmed run.

This is the exact, statistical-distance form of the sign-then-hash hop: it is one TV bound, **not**
an exact equality (stating it as equality would be false, since a fresh salt can collide with a
cached entry). It combines the pre-bridge `runtime_evalDist_liftComp` with
`tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad`. The downstream task is to bound
the right-hand bad-event probability by `collisionBound Salt qSign qHash` using regularity `hreg`
(to align the programmed value `psf.eval pk s` with the real uniform answer) and the salt-collision
union bound `probEvent_salt_collision_le_collisionBound`.

The `Finite Range`/`Inhabited Range` hypotheses supply the `IsUniformSpec (Salt × M →ₒ Range)`
instance required by the state-threading bridge; they are mild for a hash range. -/
theorem tvDist_runtime_real_programmed_le_bad [Finite Range] [Inhabited Range] {α : Type}
    (policy : OracleSpec.ProgrammingPolicy (Salt × M →ₒ Range))
    (ob : OracleComp (Salt × M →ₒ Range) α) :
    SPMF.tvDist
        ((runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α)
      ≤ Pr[fun z : α × (Salt × M →ₒ Range).QueryCache × Bool => z.2.2 = true |
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob).run
            (∅, false)].toReal := by
  haveI : Fintype Range := Fintype.ofFinite Range
  haveI : IsUniformSpec (Salt × M →ₒ Range) := IsUniformSpec.ofFintypeInhabited _
  rw [runtime_evalDist_liftComp]
  exact tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad
    (spec := (Salt × M →ₒ Range)) policy ob ∅

omit [DecidableEq Range] [SampleableType Salt] in
/-- **U2 headline (conditional on the bad-event bound).**

The sign-then-hash hop is correct up to the salt-collision birthday bound: if the programming bad
event of `policy` on the run `ob` is bounded by `collisionBound Salt qSign qHash` (the Part-C
obligation discharged by regularity + the salt-collision union bound
`probEvent_salt_collision_le_collisionBound`), then the total-variation distance between the real
GPV runtime output and the programmed (sign-then-hash) output is at most
`(collisionBound Salt qSign qHash).toReal`.

This packages the full U2 statement with the bad-event obligation taken as the
hypothesis `hbad`. The proof chains the up-to-bad core
`tvDist_runtime_real_programmed_le_bad` with `hbad`. -/
theorem tvDist_runtime_real_programmed_le_collisionBound [Finite Range] [Inhabited Range]
    [Nonempty Salt] {α : Type} (qSign qHash : ℕ)
    (policy : OracleSpec.ProgrammingPolicy (Salt × M →ₒ Range))
    (ob : OracleComp (Salt × M →ₒ Range) α)
    (hbad : Pr[ fun z : α × (Salt × M →ₒ Range).QueryCache × Bool => z.2.2 = true |
        (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob).run (∅, false)]
        ≤ collisionBound Salt qSign qHash) :
    SPMF.tvDist
        ((runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α)
      ≤ (collisionBound Salt qSign qHash).toReal := by
  refine (tvDist_runtime_real_programmed_le_bad M Salt policy ob).trans ?_
  refine ENNReal.toReal_mono ?_ hbad
  refine (ENNReal.div_lt_top ?_ ?_).ne
  · simp
  · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
    exact Fintype.card_ne_zero

/-! ## U2 (re-stated, salt-inclusive cache-hit bad event)

The headline `tvDist_runtime_real_programmed_le_collisionBound` above bounds the sign-then-hash TV
distance by the `withProgramming` *fire-on-miss* bad event over the random-oracle-only computation
`ob`. As the *salt-collision coupling and the hash-only granularity* section records, that bad event
is the wrong shape for GPV: the fire-on-miss flag is set the **first** time the policy fires on an
uncached point, so for the GPV
simulator (which programs at every fresh signing point) it fires *deterministically* — its
probability is near `1`, not `collisionBound`. Concretely, routing the salt-collision through the
fire-on-miss `hbad` is **unsound**: the genuine salt-collision probability is
`≈ collisionBound ≪ 1` while the fire-on-miss probability is `≈ 1`, so the inequality
"fire-on-miss ≤ salt-collision" needed to reuse the headline is *false* for the GPV policy. Moreover
the fresh signing salts — drawn in `unifSpec`, one step *before* each random-oracle query — are
invisible at `ob`'s granularity, so the `card / |Salt|` averaging is structurally absent from the
fire-on-miss flag.

`tvDist_runtime_real_programmed_le_collisionBound_saltInclusive` re-states U2 so its bad event is
the genuine GPV salt-collision: a fresh signing salt drawn in `unifSpec` landing in the recorded
random-oracle cache restricted to its message slice (a cache *hit* at a programmed point), modelled
by the salt-averaged process `saltSeq c qSign` of the telescope section. The per-step caches `c j`
are the recorded random-oracle inputs seen by the `j`-th signing query; the standard GPV
cache-growth bound `card (c j) ≤ j + qHash` (the `j` prior signing salts plus the up to `qHash`
adversary hash queries) is supplied as `hcache`.

Crucially, the lemma does **not** route through the headline U2's fire-on-miss `hbad`; it takes the
genuine *up-to-bad* coupling directly as `hcouple`: the total-variation distance between the real
and programmed runs is bounded by the salt-collision probability `Pr[saltSeq c qSign = true]`. This
is the correct identical-until-bad statement for the GPV game with bad event = cache-HIT salt
collision (the two runs differ only when a fresh salt collides with a recorded entry). It is
**true** (it is the real GPV up-to-bad bound, the cache-hit counterpart of the fire-on-miss
core `tvDist_runtime_real_programmed_le_bad`) and **non-vacuous** (`saltSeq c qSign` is a genuine
probabilistic process whose collision probability `probEvent_saltSeq_le_collisionBound` bounds it
strictly by `collisionBound < ⊤`, so `hcouple` is a real inequality between two `< ⊤` quantities,
not a `≤ ⊤` triviality; and the TV distance it bounds is in general positive, so it is not
vacuously `0 ≤ _`). Unlike the fire-on-miss route, `hcouple` is *satisfiable* by the GPV policy
precisely because its bad event is the small cache-hit collision rather than the deterministic
fire-on-miss.

`hcouple` names the joint-distribution coupling over the interleaved
salt-draw / random-oracle-query streams of the salt-inclusive signing run: each of the `qSign`
fresh salts is checked against the recorded cache slice of size `≤ j + qHash`, which is precisely
the `saltSeq` process. Once `hcouple` is discharged by the coupling, this lemma yields the loss-free
`tvDist ≤ (collisionBound Salt qSign qHash).toReal` consumed by the four GPV theorems.

The proof is loss-free: chain `hcouple` (TV distance ≤ `saltSeq` collision) with the
salt-averaged telescope `probEvent_saltSeq_le_collisionBound` (`saltSeq` collision ≤
`collisionBound`), then move to `ℝ` with `ENNReal.toReal_mono`. -/
omit [DecidableEq Range] in
theorem tvDist_runtime_real_programmed_le_collisionBound_saltInclusive
    [Finite Range] [Inhabited Range] [Nonempty Salt] {α : Type} (qSign qHash : ℕ)
    (policy : OracleSpec.ProgrammingPolicy (Salt × M →ₒ Range))
    (ob : OracleComp (Salt × M →ₒ Range) α)
    (c : ℕ → Finset Salt) (hcache : ∀ j, (c j).card ≤ j + qHash)
    (hcouple : (SPMF.tvDist
        ((runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α) : ℝ)
        ≤ (Pr[ (· = true) | saltSeq (Salt := Salt) c qSign]).toReal) :
    SPMF.tvDist
        ((runtime M Salt).evalDist (OracleComp.liftComp ob (unifSpec + (Salt × M →ₒ Range))))
        (liftM (StateT.run'
          (simulateQ (QueryImpl.withProgramming uniformSampleImpl policy) ob) (∅, false))
          : SPMF α)
      ≤ (collisionBound Salt qSign qHash).toReal :=
  hcouple.trans (ENNReal.toReal_mono
    (by
      refine (ENNReal.div_lt_top ?_ ?_).ne
      · simp
      · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
        exact Fintype.card_ne_zero)
    (probEvent_saltSeq_le_collisionBound Salt qSign qHash c hcache))

/-! ## Step 1 and the wiring to the headline bounds

**Step 1 (sign-then-hash ≡ real).** `gpv_tvDist_real_programmed_le_collisionBound` *consumes* the
direct front-tape coupling `gpv_tvDist_tape_runs_le_collisionBound`: after the front-tape
factorization bridges put both pinned GPV game runs into `drawList ($ᵗ Salt) qSign >>= tape-run`
shape, the per-tape identical-until-bad coupling `(A)` and the front-tape birthday bound `(B)`
discharge the salt-inclusive sign-then-hash hop `tvDist realRun progRun ≤ collisionBound`. The
front-tape coupling is invoked on the Step-1 path.

**Wiring Step 1 to the headline bounds.** Two facts connect
`gpv_tvDist_real_programmed_le_collisionBound` to the headline bounds:

1. *Game identification.* The headline LHS `adv.advantage (runtime)` is
   `Pr[= true | unforgeableExp (runtime) adv]`, whose body runs `simulateQ impl (adv.main pk)` — the
   signing oracle draws each fresh salt *internally* at an adversary-chosen point over the sum spec
   `unifSpec + (Salt × M →ₒ Range)`. Connecting this to the *pinned* hash-only run `ob` of
   `gpv_tvDist_real_programmed_le_collisionBound` (so that `abs_probOutput_toReal_sub_le_tvDist`
   converts the run-level `tvDist ≤ collisionBound` into `realAdv ≤ progAdv + collisionBound`) is
   the same deferred-sampling factorization as the front-tape coupling, now over the adversary's
   *adaptive* control flow rather than a fixed `ob`.
2. *Step 2 (collision extraction).* In the programmed sign-then-hash game every random-oracle entry
   carries the simulator's hidden short preimage; a fresh forgery on a programmed point with a
   *distinct* preimage is a collision under `psf.eval`, bounding `progAdv` by
   `collisionFindingAdvantage (reduction …)`. This is stated *pinned and true* over the concrete
   programmed forgery game and the concrete `reduction` body, with the exact-match branch handled by
   `programmedPreimageReduction`. -/

/-! ## O1: the data-processing bridge from Step-1 to a post-processed (verification) game

Step-1 (`gpv_tvDist_real_programmed_le_collisionBound`) bounds the total-variation distance between
the *forgery* distributions `realGameRun` and `progGameRun` (both `SPMF (M × (Salt × Domain))`) by
`collisionBound`. The headline games are obtained by post-processing each forgery `out = (msg, σ)`
through a verification step `k : M × (Salt × Domain) → SPMF Bool`. The lemma below is the
data-processing transfer of Step-1 across that post-processing: for *any* `SPMF`-valued
post-processor `k`, the success probability of the real post-processed game exceeds that of the
programmed post-processed game by at most `collisionBound`.

It is a pure consequence of the data-processing inequality `tvDist_bind_right_le` (binding both runs
with the same continuation `k` does not increase TV distance) chained with Step-1, transported to
`ℝ≥0∞` through the bool-valued TV bridge `abs_probOutput_toReal_sub_le_tvDist`. It carries no new
probabilistic content beyond Step-1 and is reusable for any verification post-processor. -/
theorem gpv_realGameVerify_le_progGameVerify_add_collisionBound
    [Finite Range] [Inhabited Range] [Nonempty Salt]
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (hNF : ∀ c, NeverFail (psf.trapdoorSample pk sk c))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (k : M × (Salt × Domain) → SPMF Bool) :
    Pr[= true | realGameRun psf hr M Salt adv pk sk >>= k]
      ≤ Pr[= true | progGameRun psf hr M Salt adv domainSample pk >>= k]
        + collisionBound Salt qSign qHash := by
  -- Both probabilities are `< ⊤`, so it suffices to prove the `toReal` inequality.
  have hcb_lt_top : collisionBound Salt qSign qHash < ⊤ := by
    refine ENNReal.div_lt_top ?_ ?_
    · simp
    · simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
      exact Fintype.card_ne_zero
  set pProg := Pr[= true | progGameRun psf hr M Salt adv domainSample pk >>= k] with hpProg
  rw [← ENNReal.ofReal_toReal probOutput_ne_top,
      ← ENNReal.ofReal_toReal (a := pProg) probOutput_ne_top,
      ← ENNReal.ofReal_toReal hcb_lt_top.ne]
  rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `Pr[real⋯].toReal ≤ Pr[prog⋯].toReal + tvDist(real⋯)(prog⋯)` via the bool TV bridge,
  -- then `tvDist(real⋯)(prog⋯) ≤ tvDist(real)(prog) ≤ collisionBound` (DPI + Step-1).
  have hbridge :=
    abs_probOutput_toReal_sub_le_tvDist
      (realGameRun psf hr M Salt adv pk sk >>= k)
      (progGameRun psf hr M Salt adv domainSample pk >>= k)
  have hsub :=
    (abs_le.mp hbridge).2
  have hdpi : SPMF.tvDist
        (realGameRun psf hr M Salt adv pk sk >>= k)
        (progGameRun psf hr M Salt adv domainSample pk >>= k)
      ≤ (collisionBound Salt qSign qHash).toReal :=
    le_trans (SPMF.tvDist_bind_right_le k _ _)
      (gpv_tvDist_real_programmed_le_collisionBound psf hr M Salt pk sk adv domainSample
        qSign qHash hQ hNF hreg)
  linarith [le_trans hsub hdpi]

open Classical in
omit [Fintype Salt] in
/-- **Keygen-averaging peel of the GPV unforgeability experiment (sub-build (3) of the
game-identification (N)(a)).** The success probability of the GPV unforgeability experiment is the
`SPMF`-average over the key pair `(pk, sk) ← hr.gen` of the success probability of the per-key
verify-extended WriterT signing-log experiment under the bundled `withStateOracle` random-oracle
semantics.

The GPV `keygen` is `liftM hr.gen`, a public-randomness prefix that touches neither the
random-oracle cache nor the hidden state; the keygen-peel `withStateOracle_evalDist_liftM_bind`
commutes its draw straight out of the bundled `withStateOracle` semantics as an `SPMF`-average over
`𝒟[hr.gen]`. This is the GPV-runtime analogue of the FiatShamir `roSim.run'_liftM_bind`-style
averaging step that
opens `probOutput_unforgeableExp_eq_hybridExpAtKey_real`; it isolates the keygen average so the
remaining game-identification work is a per-key WriterT-log → signed-set reconstruction. -/
theorem probOutput_unforgeableExp_eq_keygen_average
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    Pr[= true | SignatureAlg.unforgeableExp (runtime M Salt) adv]
      = Pr[= true | (𝒟[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
          (SPMFSemantics.withStateOracle
            (randomOracle : QueryImpl (Salt × M →ₒ Range)
              (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalDist
            (letI : DecidableEq M := Classical.decEq M
             letI : DecidableEq (Salt × Domain) := Classical.decEq (Salt × Domain)
             do
              let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
                  (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                    (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
                (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
                  (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                  (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                    (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
                  (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                    psf hr M Salt).signingOracle pksk.1 pksk.2
              let ((msg, σ), log) ← (simulateQ impl (adv.main pksk.1)).run
              let verified ← (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                psf hr M Salt).verify pksk.1 msg σ
              return !log.wasQueried msg && verified)] := by
  classical
  unfold SignatureAlg.unforgeableExp
  rw [show (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
        psf hr M Salt).keygen
      = (liftM hr.gen : OracleComp (unifSpec + (Salt × M →ₒ Range)) (PK × SK)) from rfl]
  refine congrArg (fun d : SPMF Bool => Pr[= true | d]) ?_
  rw [GPVHashAndSign.runtime]
  change (SPMFSemantics.withStateOracle
      (randomOracle : QueryImpl (Salt × M →ₒ Range)
        (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalDist (liftM hr.gen >>= _)
    = (𝒟[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
        (SPMFSemantics.withStateOracle
          (randomOracle : QueryImpl (Salt × M →ₒ Range)
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalDist _
  rw [withStateOracle_evalDist_liftM_bind]
  refine bind_congr fun pksk => ?_
  obtain ⟨pk, sk⟩ := pksk
  rfl

open Classical in
omit [Fintype Salt] in
/-- **Verify-extended WriterT-run fold.** Running `adv.main pk` under the WriterT signing-log stack
and then the verification read `verify pk msg σ` (as a separate `OracleComp` continuation on the
shared random-oracle base) coincides with running the *single* WriterT computation
`adv.main pk >>= fun out => (out, ·) <$> verify pk out.1 out.2`: the verification read issues no
signing query, so it leaves the WriterT log untouched (the empty log appends nothing), and
`simulateQ` distributes over the adversary-then-verify bind.  This folds the outer verification
continuation of the unforgeability experiment into the single adversary computation that the
reconstruction `map_simulateQ_gpvOuter_writerLog_eq_gpvRealImplFresh` consumes. -/
lemma simulateQ_writerImpl_verify_fold (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    ((simulateQ
        ((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
          (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
          (WriterT (QueryLog (M →ₒ (Salt × Domain)))
            (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).signingOracle pk sk)
        (adv.main pk)).run >>=
        fun z => (fun v => ((z.1, v), z.2)) <$>
          ((GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).verify pk z.1.1 z.1.2
            : OracleComp (unifSpec + (Salt × M →ₒ Range)) Bool))
      = (simulateQ
        ((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
          (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
          (WriterT (QueryLog (M →ₒ (Salt × Domain)))
            (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
          (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
            psf hr M Salt).signingOracle pk sk)
        (adv.main pk >>= fun out =>
          (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run := by
  classical
  rw [simulateQ_bind, WriterT.run_bind]
  refine bind_congr fun z => ?_
  obtain ⟨⟨msg, σ⟩, log⟩ := z
  -- The verification read is a single `.inl (.inr _)` RO query routed through the lifted base
  -- `baseW`, which logs nothing; `verify` and `gpvVerifyRead` are the same RO read + check.
  obtain ⟨r, s⟩ := σ
  -- The RHS `gpvVerifyRead` is a single `Sum.inl (Sum.inr (r, msg))` RO read; route it through the
  -- lifted base `baseW` (`simulateQ_spec_query` + `add_apply_inl` + `liftTarget_apply`).
  simp only [gpvVerifyRead, GPVHashAndSign, simulateQ_map, bind_pure_comp]
  erw [simulateQ_spec_query]
  simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
    WriterT.run_bind, WriterT.run_pure, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp_def]
  erw [WriterT.run_liftM]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, List.append_nil,
    EmptyCollection.emptyCollection]
  rfl

open Classical in
omit [Fintype Salt] in
/-- **Per-key game-identification (N)(a): WriterT-log unforgeability experiment ≡ freshness
verify-Bool game.**
The per-key body of the GPV unforgeability experiment (the keygen-peel summand of
`probOutput_unforgeableExp_eq_keygen_average`) — running `adv.main pk` under the WriterT signing-log
handler stack, then `verify`, then masking with the WriterT-log freshness check
`!log.wasQueried msg` — coincides with the freshness verify-Bool game `realGameVerifyFresh`, whose
winning Bool reads the `Finset M` signed-set carried by `gpvRealImplFlagFresh`.  This identifies the
WriterT signing log with the reconstructed signed-set across the WriterT/StateT divide, folding in
the verification continuation; it is the per-key bridge of the game-identification (N)(a). -/
lemma signedSet_eq_wasQueried
    (pk : PK) (sk : SK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (SPMFSemantics.withStateOracle
      (randomOracle : QueryImpl (Salt × M →ₒ Range)
        (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalDist
      (letI : DecidableEq M := Classical.decEq M
       letI : DecidableEq (Salt × Domain) := Classical.decEq (Salt × Domain)
       do
        let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
          (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
            (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
            (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
              psf hr M Salt).signingOracle pk sk
        let ((msg, σ), log) ← (simulateQ impl (adv.main pk)).run
        let verified ← (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).verify pk msg σ
        return !log.wasQueried msg && verified)
      = realGameVerifyFresh psf hr M Salt adv pk sk := by
  classical
  -- Reassociate the verification continuation into the WriterT run
  -- (`simulateQ_writerImpl_verify_fold`) at the `OracleComp` level, before exposing the bundled
  -- `withStateOracle` semantics.
  have heq : (letI : DecidableEq M := Classical.decEq M
       letI : DecidableEq (Salt × Domain) := Classical.decEq (Salt × Domain)
       do
        let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
          (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
            (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
            (WriterT (QueryLog (M →ₒ (Salt × Domain)))
              (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
            (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
              psf hr M Salt).signingOracle pk sk
        let ((msg, σ), log) ← (simulateQ impl (adv.main pk)).run
        let verified ← (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
          psf hr M Salt).verify pk msg σ
        return !log.wasQueried msg && verified)
      = (fun w : ((M × (Salt × Domain)) × Bool) × QueryLog (M →ₒ (Salt × Domain)) =>
            !w.2.wasQueried w.1.1.1 && w.1.2) <$>
          (simulateQ ((HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
              (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
              (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
              (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                psf hr M Salt).signingOracle pk sk)
            (adv.main pk >>= fun out =>
              (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run := by
    rw [← simulateQ_writerImpl_verify_fold]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    refine bind_congr fun x => bind_congr fun v => congrArg pure ?_
    congr!
  rw [heq, withStateOracle_evalDist_eq, simulateQ_map, StateT.run'_eq, StateT.run_map]
  simp only [Functor.map_map]
  simp only [not_wasQueried_eq_decide_not_mem_toFinset]
  -- Factor the freshness mask through the kernel's `(output, cache, signedSet)` reshaping, then
  -- rewrite the WriterT run as the freshness vehicle `gpvRealImplFresh` via the kernel.
  rw [show ((fun a : (((M × (Salt × Domain)) × Bool) × QueryLog (M →ₒ (Salt × Domain))) ×
        (Salt × M →ₒ Range).QueryCache =>
      decide (a.1.1.1.1 ∉ (List.map (fun e => e.1) a.1.2).toFinset) && a.1.1.2) <$>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp) +
          (randomOracle : QueryImpl (Salt × M →ₒ Range)
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)))
        ((simulateQ ((HasQuery.toQueryImpl (spec := unifSpec + (Salt × M →ₒ Range))
            (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
              (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
            (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
              psf hr M Salt).signingOracle pk sk)
          (adv.main pk >>= fun out =>
            (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run)).run
        (∅ : (Salt × M →ₒ Range).QueryCache))
      = (fun z : ((M × (Salt × Domain)) × Bool) ×
            (Salt × M →ₒ Range).QueryCache × Finset M =>
          decide (z.1.1.1 ∉ z.2.2) && z.1.2) <$>
        ((fun z : (((M × (Salt × Domain)) × Bool) × QueryLog (M →ₒ (Salt × Domain))) ×
              (Salt × M →ₒ Range).QueryCache =>
            (z.1.1, z.2, (z.1.2.map (fun e => e.1)).toFinset)) <$>
          (simulateQ (gpvOuter M Salt)
            ((simulateQ ((HasQuery.toQueryImpl (spec := unifSpec + (Salt × M →ₒ Range))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                  (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                    (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
                (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                  psf hr M Salt).signingOracle pk sk)
              (adv.main pk >>= fun out =>
                (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run)).run
            (∅ : (Salt × M →ₒ Range).QueryCache)) from by rw [Functor.map_map]; rfl,
    map_simulateQ_gpvOuter_writerLog_eq_gpvRealImplFresh]
  -- Bridge the flag-free run back to the flag handler that `realGameVerifyFresh` carries: the flag
  -- is passive, so projecting it away (`map_run_gpvRealImplFlagFresh_proj_flag`) recovers the
  -- flag-free run.
  rw [realGameVerifyFresh, ← map_run_gpvRealImplFlagFresh_proj_flag psf hr M Salt pk sk
    (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)
    ((∅, ∅), false)]
  simp only [Functor.map_map, Prod.map, id_eq]

omit [Fintype Salt] in
/-- **GPV freshness-drop (Phase-B game-hop), mechanical.** The GPV EUF-CMA advantage is bounded by
the success probability of the same experiment with the freshness check dropped
(`unforgeableExpNoFresh`). This instantiates the generic
`SignatureAlg.unforgeableAdv.advantage_le_unforgeableExpNoFresh` for the concrete GPV `runtime`,
discharging its `h_pull` runtime-factoring obligation by the `withStateOracle` map-commutation
`SPMFSemantics.withStateOracle_evalDist_bind_pure` (the GPV `runtime` is the bundled
`withStateOracle randomOracle ∅`). It is a pure runtime-bookkeeping bridge with no probabilistic
content: dropping the freshness check can only increase the success probability. -/
theorem gpv_advantage_le_unforgeableExpNoFresh
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    adv.advantage (runtime M Salt)
      ≤ Pr[= true | SignatureAlg.unforgeableExpNoFresh (runtime M Salt) adv] := by
  refine SignatureAlg.unforgeableAdv.advantage_le_unforgeableExpNoFresh
    (runtime M Salt) (fun {α β} f mx => ?_) adv
  -- `runtime.evalDist (mx >>= pure ∘ f) = f <$> runtime.evalDist mx` is the `withStateOracle`
  -- map-commutation at the empty cache.
  change (SPMFSemantics.withStateOracle _ ∅).evalDist (mx >>= fun x => pure (f x))
    = f <$> (SPMFSemantics.withStateOracle _ ∅).evalDist mx
  exact SPMFSemantics.withStateOracle_evalDist_bind_pure _ ∅ mx f

open Classical in
/-- **Game-identification (N): the GPV EUF-CMA advantage is bounded by the keygen-averaged
programmed freshness verify-Bool game plus `collisionBound`.** Chains the keygen-averaging peel
`probOutput_unforgeableExp_eq_keygen_average`, the per-key WriterT-log → signed-set reconstruction
`signedSet_eq_wasQueried`, and the real↔programmed coupling hop
`gpv_realGameVerifyFresh_le_progGameVerifyFresh_add_collisionBound`, averaged over the key pair
`(pk, sk) ← hr.gen`.  It reduces closing the split bound to bounding the programmed game
`progGameVerifyFresh` (the remaining reservoir-sampling extraction). -/
theorem gpv_advantage_le_progGameVerifyFreshAvg_add_collisionBound
    [Inhabited Range] [Nonempty Salt]
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    adv.advantage (runtime M Salt) ≤
      Pr[= true | (𝒟[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
        progGameVerifyFresh psf hr M Salt adv domainSample pksk.1]
        + collisionBound Salt qSign qHash := by
  classical
  rw [SignatureAlg.unforgeableAdv.advantage,
    probOutput_unforgeableExp_eq_keygen_average psf hr M Salt adv]
  rw [show (fun pksk : PK × SK =>
        (SPMFSemantics.withStateOracle
          (randomOracle : QueryImpl (Salt × M →ₒ Range)
            (StateT ((Salt × M →ₒ Range).QueryCache) ProbComp)) ∅).evalDist
          (letI : DecidableEq M := Classical.decEq M
           letI : DecidableEq (Salt × Domain) := Classical.decEq (Salt × Domain)
           do
            let impl : QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) :=
              (HasQuery.toQueryImpl (spec := (unifSpec + (Salt × M →ₒ Range)))
                (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))).liftTarget
                (WriterT (QueryLog (M →ₒ (Salt × Domain)))
                  (OracleComp (unifSpec + (Salt × M →ₒ Range)))) +
                (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
                  psf hr M Salt).signingOracle pksk.1 pksk.2
            let ((msg, σ), log) ← (simulateQ impl (adv.main pksk.1)).run
            let verified ← (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range)))
              psf hr M Salt).verify pksk.1 msg σ
            return !log.wasQueried msg && verified))
      = (fun pksk : PK × SK => realGameVerifyFresh psf hr M Salt adv pksk.1 pksk.2) from
    funext fun pksk => signedSet_eq_wasQueried psf hr M Salt pksk.1 pksk.2 adv]
  rw [probOutput_bind_eq_tsum (𝒟[hr.gen] : SPMF (PK × SK)), probOutput_bind_eq_tsum
    (𝒟[hr.gen] : SPMF (PK × SK))]
  -- Average the per-key coupling hop over `(pk, sk) ← hr.gen`: weight each per-key bound by its
  -- keygen mass `Pr[= x | 𝒟[hr.gen]]`, pull the constant `collisionBound` out using
  -- `∑' x, Pr[= x | 𝒟[hr.gen]] ≤ 1`.
  have hper : ∀ x ∈ support hr.gen,
      Pr[= true | realGameVerifyFresh psf hr M Salt adv x.1 x.2] ≤
        Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1]
          + collisionBound Salt qSign qHash := fun x hx =>
    gpv_realGameVerifyFresh_le_progGameVerifyFresh_add_collisionBound psf hr M Salt
      x.1 x.2 adv domainSample qSign qHash (hQ x.1)
      (fun c => hNF x.1 x.2 hx c) (hreg x.1 x.2 hx)
  calc ∑' x : PK × SK,
        Pr[= x | 𝒟[hr.gen]] * Pr[= true | realGameVerifyFresh psf hr M Salt adv x.1 x.2]
      ≤ ∑' x : PK × SK, (Pr[= x | 𝒟[hr.gen]]
            * Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1]
          + Pr[= x | 𝒟[hr.gen]] * collisionBound Salt qSign qHash) :=
        ENNReal.tsum_le_tsum fun x => by
          by_cases hx : x ∈ support hr.gen
          · rw [← mul_add]; gcongr; exact hper x hx
          · have hzero : Pr[= x | (𝒟[hr.gen] : SPMF (PK × SK))] = 0 :=
              probOutput_eq_zero_of_not_mem_support (mx := hr.gen) hx
            simp [hzero]
    _ = ∑' x : PK × SK, (Pr[= x | 𝒟[hr.gen]]
            * Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1])
          + (∑' x : PK × SK, Pr[= x | 𝒟[hr.gen]]) * collisionBound Salt qSign qHash := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ ∑' x : PK × SK, (Pr[= x | 𝒟[hr.gen]]
            * Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1])
          + 1 * collisionBound Salt qSign qHash := by
        gcongr
        exact tsum_probOutput_le_one
    _ = ∑' x : PK × SK, (Pr[= x | 𝒟[hr.gen]]
            * Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample x.1])
          + collisionBound Salt qSign qHash := by rw [one_mul]

open Classical in
/-- **The forger queries its forgery point (standard random-oracle well-formedness).** For every
public key, every forgery `(msg, (r, s))` the adversary outputs in the programmed sign-then-hash
game lands on a random-oracle point `(r, msg)` that was already programmed during the adversary's
run — i.e. the forger queried `RO(r, msg)` before forging, so the verification read is a cache hit.
This is the textbook ROM convention (matching the "fresh forgery on a *programmed* point" framing of
the collision extraction): any adversary is transformed into one satisfying it by appending a single
hash query at its forgery point (absorbed into `qHash`).  It rules out the degenerate
"forge on a never-queried point" case, in which the verification read would program the point
*fresh* — a value independent of the forged preimage — which neither the collision nor the
programmed-preimage reduction observes. -/
def ForgesQueriedPoint
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) : Prop :=
  ∀ (pk : PK), ∀ z ∈ support ((simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
      (adv.main pk)).run (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)),
    z.2.1.1 (z.1.2.1, z.1.1) ≠ none

omit [Fintype Salt] in
/-- **SL-C: the collision-finding advantage unfolds to an averaged collision-event
probability.** The success probability of the collision reduction in the keyed collision game is
exactly the chance, over a freshly generated public key `pk` and the reduction's candidate pair
`(x₁, x₂)`, that the pair is a genuine `psf.eval`-collision of two distinct short preimages.  This
exposes the collision event as a plain `Pr[= true | …]` so the Step-2 extraction can bound the
programmed game's distinct-collision mass against it. -/
theorem collisionFindingAdvantage_reduction_eq [DecidableEq Domain]
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) :
    collisionFindingAdvantage (psf := psf) (hr := hr)
        (reduction psf hr M Salt adv domainSample)
      = Pr[= true | (do
          let pk ← (Prod.fst <$> hr.gen : ProbComp PK)
          let xs ← reduction psf hr M Salt adv domainSample pk
          pure (decide (xs.1 ≠ xs.2) &&
            decide (psf.eval pk xs.1 = psf.eval pk xs.2) &&
            psf.isShort xs.1 && psf.isShort xs.2) : ProbComp Bool)] := by
  unfold collisionFindingAdvantage collisionFindingExp
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Hidden programmed preimages are short.** Every preimage `s` in the support of the forward
sampler `domainSample pk` is accepted by the verifier's shortness predicate (`psf.isShort s`),
under PSF correctness `hcorrect` and the regularity equality `hreg` at `(pk, sk)`.

The forward-sampled `(psf.eval pk s, s)` lands in the support of the regularity LHS, hence — by the
distributional equality `hreg` — in the support of the RHS `do c ← $ᵗ Range; s' ← trapdoorSample pk
sk c; pure (c, s')`.  That exhibits `s` as a trapdoor preimage of the matching target `c`, so
`hcorrect` certifies `psf.isShort s`.  This is the shortness witness for the simulator's hidden
preimage recorded at each programmed random-oracle entry by the collision reduction. -/
lemma isShort_of_mem_support_domainSample
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hcorrect : psf.CorrectAt pk sk)
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (s : Domain) (hs : s ∈ support (domainSample pk)) :
    psf.isShort s = true := by
  classical
  have hmemL : (psf.eval pk s, s) ∈
      support (do let s' ← domainSample pk; pure (psf.eval pk s', s') :
        ProbComp (Range × Domain)) := by
    simp only [support_bind, support_pure, Set.mem_iUnion]
    exact ⟨s, hs, rfl⟩
  have hmemR : (psf.eval pk s, s) ∈
      support (do let c ← ($ᵗ Range); let s' ← psf.trapdoorSample pk sk c; pure (c, s') :
        ProbComp (Range × Domain)) := by
    rw [← mem_support_evalDist_iff, ← hreg, mem_support_evalDist_iff]
    exact hmemL
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    Prod.mk.injEq] at hmemR
  obtain ⟨c, _hc, s', hs', heq1, heq2⟩ := hmemR
  subst heq2
  exact (hcorrect c s hs').2

omit [SampleableType Range] [Fintype Salt] in
/-- **The verification read is table-passive on a cache hit.** When the forged point `(r, msg)` is
already cached in the combined run state `st` with value `v`, running the GPV verification read
`gpvVerifyRead pk (msg, (r, s))` under the combined handler from `st` reads back `v`, returns the
verification Bool `decide (psf.eval pk s = v) && psf.isShort s`, and leaves the *entire* combined
state — cache, signed-set, flag, and hidden table — unchanged.  The verification read issues a
single random-oracle query at the forged point, which on a hit is a pure `get`/return. -/
lemma run_combined_gpvVerifyRead_of_cache_hit (domainSample : PK → ProbComp Domain) (pk : PK)
    (msg : M) (r : Salt) (s : Domain) (v : Range)
    (st : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hhit : st.1.1.1 (r, msg) = some v) :
    (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
        (gpvVerifyRead psf M Salt pk (msg, (r, s)))).run st =
      pure (decide (psf.eval pk s = v) && psf.isShort s, st) := by
  rw [gpvVerifyRead]
  rw [simulateQ_bind, simulateQ_query, StateT.run_bind]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, StateT.run_map, simulateQ_pure,
    StateT.run_pure]
  rw [progGameRunImplCombined_run_inl_inr, hhit]
  simp only [id_eq, map_pure, pure_bind]

omit [SampleableType Range] [Fintype Salt] in
/-- **The verification continuation is table-passive on a cache hit.** The `verifyKont`-shaped
continuation `(out, ·) <$> gpvVerifyRead pk out` of the freshness verify game, run under the
combined handler from a state `st` whose cache hits the forged point with value `v`, returns the
pair of the forgery output `out` and the verification Bool, leaving the entire combined state
unchanged. -/
lemma run_combined_verifyKont_of_cache_hit (domainSample : PK → ProbComp Domain) (pk : PK)
    (msg : M) (r : Salt) (s : Domain) (v : Range)
    (st : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hhit : st.1.1.1 (r, msg) = some v) :
    (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
        ((fun w => ((msg, (r, s)), w)) <$>
          gpvVerifyRead psf M Salt pk (msg, (r, s)))).run st =
      pure (((msg, (r, s)), decide (psf.eval pk s = v) && psf.isShort s), st) := by
  rw [simulateQ_map, StateT.run_map,
    run_combined_gpvVerifyRead_of_cache_hit psf M Salt domainSample pk msg r s v st hhit]
  simp only [map_pure]

omit [Fintype Salt] in
/-- **`hForge` transported to the combined run.** Under `ForgesQueriedPoint`, every final state of
the combined run over `adv.main pk` (from the empty start) has its cache defined at the forged point
`(r⋆, msg⋆)`.  Projecting the combined run onto the game handler
(`map_run_progGameRunImplCombined_proj_table`) sends each combined final state to a game final
state, to which `hForge` applies; the cache component is preserved by the table projection. -/
lemma combined_cache_forge_point_ne_none (domainSample : PK → ProbComp Domain) (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (w : (M × (Salt × Domain)) ×
      ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)))
    (hw : w ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
      (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
        fun _ => none))) :
    w.2.1.1.1 (w.1.2.1, w.1.1) ≠ none := by
  have hproj := map_run_progGameRunImplCombined_proj_table psf M Salt domainSample pk
    (adv.main pk) ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)
  have hmem : (Prod.map id
      (Prod.fst : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain) → ((Salt × M →ₒ Range).QueryCache × Finset M) × Bool)) w ∈
      support ((simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
        (adv.main pk)).run (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)) := by
    rw [← hproj, support_map]
    exact ⟨w, hw, rfl⟩
  exact hForge pk _ hmem

open Classical in
omit [Fintype Salt] in
/-- **The programmed verify game success is a winning event on the combined run.** Projecting the
combined run over `adv.main pk >>= verifyKont` onto the game handler recovers the programmed
freshness verify game (`map_run_progGameRunImplCombined_proj_table`), so the game's success
probability equals the probability, over the combined run, of the *winning event*: the forged
message is fresh (not in the signed set) and the verification Bool is `true`. -/
lemma progGameVerifyFresh_eq_probEvent_combined (domainSample : PK → ProbComp Domain) (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pk]
      = Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
            ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
              (decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true |
          (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
            (adv.main pk >>= fun out =>
              (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
            ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)] := by
  have hgame : Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pk]
      = Pr[= true | (fun z : ((M × (Salt × Domain)) × Bool) ×
            (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) =>
            decide (z.1.1.1 ∉ z.2.1.2) && z.1.2) <$>
          (simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk)
            (adv.main pk >>= fun out =>
              (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
            (((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false)] := rfl
  rw [hgame, ← map_run_progGameRunImplCombined_proj_table psf M Salt domainSample pk
    (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)
    ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
    ← probEvent_eq_eq_probOutput, Functor.map_map, probEvent_map]
  rfl

open Classical in
omit [Fintype Salt] in
/-- **The collision-reduction success is a collision event on the combined run.** The collision
reduction runs `reductionImpl` over `adv.main pk` and reads its hidden table at the forged point;
projecting the combined run onto `reductionImpl` (`map_run_progGameRunImplCombined_proj_reduction`)
re-expresses the reduction's collision-success probability as the probability, over the combined run
*of `adv.main pk` alone*, that the table records a hidden preimage `sHidden` at the forged point
with `(sHidden, s⋆)` a genuine `psf.eval`-collision of two distinct short preimages. -/
lemma reduction_collision_eq_probEvent_combined [DecidableEq Domain]
    (domainSample : PK → ProbComp Domain) (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    Pr[= true | (reduction psf hr M Salt adv domainSample pk >>= fun xs =>
        pure (decide (xs.1 ≠ xs.2) && decide (psf.eval pk xs.1 = psf.eval pk xs.2) &&
          psf.isShort xs.1 && psf.isShort xs.2) : ProbComp Bool)]
      = Pr[fun w : (M × (Salt × Domain)) ×
            ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
              ∃ sHidden : Domain, w.2.2 (w.1.2.1, w.1.1) = some sHidden ∧
                (decide (sHidden ≠ w.1.2.2) &&
                  decide (psf.eval pk sHidden = psf.eval pk w.1.2.2) &&
                  psf.isShort sHidden && psf.isShort w.1.2.2) = true |
          (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
            (adv.main pk)).run
            ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)] := by
  rw [reduction_eq_run_reductionImpl psf hr M Salt adv domainSample pk]
  rw [← map_run_progGameRunImplCombined_proj_reduction psf M Salt domainSample pk
    (adv.main pk) ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)]
  rw [← probEvent_eq_eq_probOutput, bind_assoc, bind_map_left, probEvent_bind_eq_tsum]
  conv_rhs => rw [← bind_pure ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
    (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)), probEvent_bind_eq_tsum]
  refine tsum_congr fun w => ?_
  congr 1
  rcases w with ⟨out, st⟩
  obtain ⟨msgStar, rStar, sStar⟩ := out
  simp only [Prod.map, id_eq]
  rcases hlk : st.2 (rStar, msgStar) with _ | sHidden
  · simp only [hlk, pure_bind, probEvent_pure, ne_eq, not_true_eq_false,
      decide_false, Bool.false_and]
    simp
  · simp only [hlk, pure_bind, probEvent_pure, Option.some.injEq, exists_eq_left']

open Classical in
omit [Fintype Salt] in
/-- **Pointwise distinct-collision transfer.** For any final state `(out, st)` of the combined run
over `adv.main pk` whose forged point is cached (guaranteed by `hForge`), the distinct-preimage
winning event on the verify-extended run implies the collision event on the table: the cache hit at
the forged point exhibits a hidden preimage `sHidden` with `psf.eval pk sHidden = psf.eval pk s⋆`
(the verifier's check), with `sHidden ≠ s⋆` (distinctness), and both short (`s⋆` by the verifier,
`sHidden` by `hcorrect`/`hreg` on the drawn preimage). -/
lemma distinct_implies_collision_pointwise [DecidableEq Domain]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hcorrect : psf.CorrectAt pk sk)
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (out : M × (Salt × Domain))
    (st : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hmem : (out, st) ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
      (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
        fun _ => none)))
    (vb : Bool)
    (hvb : vb = (decide (psf.eval pk out.2.2 =
      (st.1.1.1 (out.2.1, out.1)).getD (psf.eval pk out.2.2)) && psf.isShort out.2.2))
    (hwin : (decide (out.1 ∉ st.1.1.2) && vb) = true)
    (hdist : st.2 (out.2.1, out.1) ≠ some out.2.2) :
    ∃ sHidden : Domain, st.2 (out.2.1, out.1) = some sHidden ∧
      (decide (sHidden ≠ out.2.2) && decide (psf.eval pk sHidden = psf.eval pk out.2.2) &&
        psf.isShort sHidden && psf.isShort out.2.2) = true := by
  -- Cache hit at the forged point (from `hForge`).
  have hcache_ne : st.1.1.1 (out.2.1, out.1) ≠ none :=
    combined_cache_forge_point_ne_none psf hr M Salt domainSample pk adv hForge (out, st) hmem
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hcache_ne
  -- Cache ⇒ table coherence: the hidden preimage and the eval relation.
  have hci : combinedCacheImpliesTableInv psf M Salt pk st :=
    progGameRunImplCombined_run_cacheImpliesTable psf M Salt domainSample pk (adv.main pk)
      _ (by intro t v ht; simp at ht) (out, st) hmem
  obtain ⟨sHidden, htbl, hveq⟩ := hci (out.2.1, out.1) v hv
  -- Table values are drawn preimages, hence short.
  have htd : combinedTableInDomainInv M Salt domainSample pk st :=
    progGameRunImplCombined_run_tableInDomain psf M Salt domainSample pk (adv.main pk)
      _ (by intro t d ht; simp at ht) (out, st) hmem
  have hHidden_mem : sHidden ∈ support (domainSample pk) := htd (out.2.1, out.1) sHidden htbl
  have hHidden_short : psf.isShort sHidden = true :=
    isShort_of_mem_support_domainSample psf domainSample pk sk hcorrect hreg sHidden hHidden_mem
  -- Unpack the winning Bool: verification holds, so `eval pk s⋆ = v` and `isShort s⋆`.
  rw [hvb] at hwin
  simp only [hv, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨_hfresh, hverify_eq, hshort_star⟩ := hwin
  -- Assemble the collision.
  refine ⟨sHidden, htbl, ?_⟩
  have hsHidden_ne : sHidden ≠ out.2.2 := by
    intro h; exact hdist (h ▸ htbl)
  have heval : psf.eval pk sHidden = psf.eval pk out.2.2 := by
    rw [← hveq, ← hverify_eq]
  simp only [hsHidden_ne, hverify_eq, hshort_star, hHidden_short, heval, decide_true,
    Bool.and_self, ne_eq, not_false_eq_true]

omit [SampleableType Range] [SampleableType Salt] in
/-- **Table-domain of a combined-run state.** The finite set of random-oracle keys `(r, m)` at
which the hidden-preimage table `s.2` of a `progGameRunImplCombined` state has recorded an entry.
Each entry was programmed by exactly one signing (`.inr`) or random-oracle-miss (`.inl (.inr)`)
query, so its cardinality is the number of programmed entries — the reservoir over which the
exact-match reduction guesses (`combined_run_table_card_le`). -/
noncomputable def combinedTableSupport [Fintype M]
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) :
    Finset (Salt × M) :=
  Finset.univ.filter (fun t => s.2 t ≠ none)

omit [DecidableEq Range] [SampleableType Range] [SampleableType Salt] in
/-- **Table-domain growth on writing one entry.** Overwriting the table at a single key `q` with
`some sd` enlarges the table-domain by at most one element (the key `q`); every other key's status
is unchanged. -/
lemma combinedTableSupport_write_card_le [Fintype M]
    (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (q : Salt × M) (sd : Domain)
    (s' : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (hs' : s'.2 = fun t' => if t' = q then some sd else s.2 t') :
    (combinedTableSupport M Salt s').card ≤ (combinedTableSupport M Salt s).card + 1 := by
  classical
  refine le_trans (Finset.card_le_card ?_)
    (le_trans (Finset.card_insert_le q (combinedTableSupport M Salt s)) (by rw [add_comm]))
  intro t ht
  simp only [combinedTableSupport, Finset.mem_filter, Finset.mem_univ, true_and, hs'] at ht
  simp only [Finset.mem_insert, combinedTableSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases htq : t = q
  · exact Or.inl htq
  · rw [if_neg htq] at ht
    exact Or.inr ht

omit [DecidableEq Range] [SampleableType Range] in
/-- **Table-domain growth through the whole combined run.** Over any adversary computation `oa`
making at most `qS` signing queries and `qH` random-oracle queries, every final state of the
combined run `progGameRunImplCombined` enlarges the table-domain by at most `qS + qH` entries:
uniform steps and random-oracle cache hits leave the table untouched, while each signing step and
each random-oracle miss writes a single key (`combinedTableSupport_write_card_le`), charged against
the residual signing or hash budget. -/
lemma combinedTableSupport_run_card_le [Fintype M] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
      (qS qH : ℕ),
      oa.IsQueryBoundP (· matches .inr _) qS →
      oa.IsQueryBoundP (· matches .inl (.inr _)) qH →
      ∀ y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run s),
        (combinedTableSupport M Salt y.2).card
          ≤ (combinedTableSupport M Salt s).card + qS + qH := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s qS qH _ _ y hy
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact le_add_right (Nat.le_add_right _ _)
  | query_bind t mx ih =>
      intro s qS qH hQS hQH y hy
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hy
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQS hQH
      obtain ⟨hQS1, hQS2⟩ := hQS
      obtain ⟨hQH1, hQH2⟩ := hQH
      rcases (mem_support_bind_iff _ _ _).1 hy with ⟨⟨pv, pst⟩, hps, hy⟩
      rcases t with (n | mc) | msg
      · -- uniform query: table untouched, both budgets pass through
        rw [progGameRunImplCombined_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, hpv, hpst⟩ := hps
        subst pst
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        exact ih pv s qS qH hbS hbH y hy
      · -- random-oracle query: hit leaves the table fixed, miss writes one key
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqH : 0 < qH := by simpa using hQH1
        rw [progGameRunImplCombined_run_inl_inr] at hps
        cases hq : s.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            subst pst
            exact le_trans (ih pv s qS (qH - 1) hbS hbH y hy) (by omega)
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨sd, -, -, hpst⟩ := hps
            have hgrow : (combinedTableSupport M Salt pst).card
                ≤ (combinedTableSupport M Salt s).card + 1 :=
              combinedTableSupport_write_card_le M Salt s mc sd pst (by rw [hpst])
            exact le_trans (ih pv pst qS (qH - 1) hbS hbH y hy) (by omega)
      · -- signing query: writes one key, charged against the signing budget
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqS : 0 < qS := by simpa using hQS1
        rw [progGameRunImplCombined_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, sd, -, -, hpst⟩ := hps
        have hgrow : (combinedTableSupport M Salt pst).card
            ≤ (combinedTableSupport M Salt s).card + 1 :=
          combinedTableSupport_write_card_le M Salt s (r, msg) sd pst (by rw [hpst])
        exact le_trans (ih pv pst (qS - 1) qH hbS hbH y hy) (by omega)

omit [DecidableEq Range] [SampleableType Range] in
/-- **D1 — entry-count bound.** Starting from the empty hidden-preimage table, every final state of
the combined run of an adversary `oa` obeying `signHashQueryBound` records at most `qSign + qHash`
table entries.  This is the reservoir size over which the exact-match programmed-preimage reduction
samples its embedding slot in the GPV Step-2 collision extraction. -/
lemma combined_run_table_card_le [Fintype M] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (qSign qHash : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := β)
      (oa := oa) (qSign := qSign) (qHash := qHash))
    {y : β × ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
      ((Salt × M) → Option Domain))}
    (hmem : y ∈ support ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa).run
      ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none))) :
    (combinedTableSupport M Salt y.2).card ≤ qSign + qHash := by
  have hbase : (combinedTableSupport M Salt
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
        (fun _ => none : (Salt × M) → Option Domain)))).card = 0 := by
    simp [combinedTableSupport]
  refine le_trans (combinedTableSupport_run_card_le psf M Salt domainSample pk oa _ qSign qHash
    hQ.1 hQ.2 y hmem) ?_
  rw [hbase]
  omega

open Classical in
omit [Fintype Salt] in
/-- **Distinct-collision transfer (probability level).** The distinct-preimage winning mass on the
combined verify-extended run is bounded by the collision event on the combined run of `adv.main pk`.
The verify continuation is table-passive on the cache hit (`run_combined_verifyKont_of_cache_hit`),
so the distinct event on the verify-extended run reduces, support-pointwise, to the distinct event
on `adv.main pk`'s final state, which the pointwise transfer `distinct_implies_collision_pointwise`
turns into the table collision. -/
lemma gpv_perKey_distinct_le_collision [DecidableEq Domain]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK)
    (hcorrect : psf.CorrectAt pk sk)
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample) :
    Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
            (decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) ≠ some w.1.1.2.2 |
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
          (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ Pr[fun w : (M × (Salt × Domain)) ×
            ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
              ∃ sHidden : Domain, w.2.2 (w.1.2.1, w.1.1) = some sHidden ∧
                (decide (sHidden ≠ w.1.2.2) &&
                  decide (psf.eval pk sHidden = psf.eval pk w.1.2.2) &&
                  psf.isShort sHidden && psf.isShort w.1.2.2) = true |
          (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
            (adv.main pk)).run
            ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)] := by
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum_subtype]
  conv_rhs => rw [← bind_pure ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
    (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)), probEvent_bind_eq_tsum_subtype]
  refine ENNReal.tsum_le_tsum fun p => ?_
  gcongr
  obtain ⟨⟨out, st⟩, hmem⟩ := p
  obtain ⟨msg, r, s⟩ := out
  rw [run_combined_verifyKont_of_cache_hit psf M Salt domainSample pk msg r s
      ((st.1.1.1 (r, msg)).getD (psf.eval pk s)) st ?_, probEvent_pure, probEvent_pure]
  · by_cases hwin : (decide (msg ∉ st.1.1.2) &&
        (decide (psf.eval pk s = (st.1.1.1 (r, msg)).getD (psf.eval pk s)) &&
          psf.isShort s)) = true ∧ st.2 (r, msg) ≠ some s
    · obtain ⟨sHidden, htbl, hcoll⟩ :=
        distinct_implies_collision_pointwise psf hr M Salt domainSample pk sk hcorrect hreg adv
          hForge (msg, (r, s)) st hmem _ rfl hwin.1 hwin.2
      rw [if_pos hwin, if_pos ⟨sHidden, htbl, hcoll⟩]
    · rw [if_neg hwin]
      exact zero_le'
  · have hcache_ne : st.1.1.1 (r, msg) ≠ none :=
      combined_cache_forge_point_ne_none psf hr M Salt domainSample pk adv hForge
        ((msg, (r, s)), st) hmem
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hcache_ne
    rw [hv, Option.getD_some]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [DecidableEq M] [DecidableEq Salt]
  [SampleableType Salt] [Fintype Salt] in
/-- **Reservoir per-step embedding mass.** At the `k`-th programmed entry the reservoir step of
`programmedPreimageReduction` draws `b ← $ᵗ Fin (k + 1)` and embeds the external target precisely
when `b = 0`, i.e. with probability `1 / (k + 1)`.  This is the atomic per-entry win probability of
the reservoir-sampling embedding: summing it telescopes to the uniform `1 / N` over the `N`
programmed entries that drives the multi-target `qSign + qHash` guessing loss. -/
lemma probOutput_reservoirStep_win (k : ℕ) :
    Pr[= (0 : Fin (k + 1)) | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))]
      = ((k : ℝ≥0∞) + 1)⁻¹ := by
  rw [probOutput_uniformSample]
  simp [Fintype.card_fin]

open Classical in
omit [DecidableEq Range] [SampleableType Range] [DecidableEq M] [DecidableEq Salt]
  [SampleableType Salt] [Fintype Salt] in
/-- **Reservoir per-step miss mass.** Complementary to `probOutput_reservoirStep_win`: at the
`k`-th programmed entry the reservoir step keeps the previous winner (draws `b ≠ 0`) with
probability `k / (k + 1)`.  This is the per-entry survival factor whose telescoping product over a
trace of `N` entries gives each fixed entry the uniform reservoir mass `1 / N`. -/
lemma probEvent_reservoirStep_miss (k : ℕ) :
    Pr[(· ≠ (0 : Fin (k + 1))) | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))]
      = (k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1) := by
  rw [probEvent_uniformSample]
  simp only [Fintype.card_fin]
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Fintype.card_fin]

/-- **Pure reservoir winner-index process.** This abstracts the winner-selection coins of
`programmedPreimageReduction` away from all cache/value data: it runs `n` reservoir steps, and at
step `k` (the `k`-th programmed entry, with running count `k`) draws the reservoir coin
`b ← $ᵗ Fin (k + 1)`; on `b = 0` the new entry `k` becomes the winner, otherwise the current winner
survives.  The recorded winner is the index of the entry at which the reduction would embed its
external target.  Its winner marginal is the data-independent core of the reservoir analysis:
`probOutput_reservoirWinnerIndex_eq` shows each of the `N` entries is the winner with probability
exactly `1 / N`. -/
noncomputable def reservoirWinnerIndex : ℕ → ProbComp (Option ℕ)
  | 0 => pure none
  | k + 1 => do
      let w ← reservoirWinnerIndex k
      let b ← ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))
      pure (if b = 0 then some k else w)

/-- One-step unfolding of `reservoirWinnerIndex` as an explicit double bind, used to feed the
per-step reservoir atoms (`probOutput_reservoirStep_win` / `probEvent_reservoirStep_miss`). -/
lemma reservoirWinnerIndex_succ (k : ℕ) :
    reservoirWinnerIndex (k + 1) = (reservoirWinnerIndex k >>= fun w =>
      ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1))) >>= fun b =>
        pure (if b = 0 then some k else w)) := rfl

/-- **Reservoir survival sum.** The total mass of the non-winning coins `b ≠ 0` at the `k`-th
reservoir step is `k / (k + 1)`; this is `probEvent_reservoirStep_miss` rephrased as a `tsum`, the
per-step survival factor of a fixed prior winner. -/
lemma tsum_reservoirStep_survival (k : ℕ) :
    (∑' x : Fin (k + 1),
        (if x ≠ 0 then Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] else 0))
      = (k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1) := by
  rw [← probEvent_eq_tsum_ite, probEvent_uniformSample]
  simp only [Fintype.card_fin]
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Fintype.card_fin]

/-- **Reservoir step, earlier target.** At the `k`-th reservoir step, for a fixed prior winner `w`
and a target index `j ≠ k`, the step lands on `some j` exactly when the coin misses (`b ≠ 0`) and
the prior winner already equals `some j`; that mass is the survival factor `k / (k + 1)` when
`w = some j`, and `0` otherwise. -/
lemma probOutput_reservoirStep_ne (k : ℕ) (w : Option ℕ) (j : ℕ) (hjk : j ≠ k) :
    Pr[= some j | (($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1))) >>= fun b =>
        pure (if b = 0 then some k else w) : ProbComp (Option ℕ))]
      = (if w = some j then ((k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1)) else 0) := by
  rw [probOutput_bind_eq_tsum]
  simp only [probOutput_pure]
  have hrw : ∀ x : Fin (k + 1),
      Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] *
        (if some j = if x = 0 then some k else w then (1 : ℝ≥0∞) else 0)
        = (if x ≠ 0 then Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] else 0) *
            (if w = some j then (1 : ℝ≥0∞) else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp only [if_true, ne_eq, not_true_eq_false, if_false, zero_mul]
      rw [if_neg (fun h => hjk (Option.some.inj h)), mul_zero]
    · rw [if_neg hx, if_pos (show x ≠ 0 from hx)]
      by_cases hw : w = some j
      · rw [if_pos hw, if_pos hw.symm]
      · rw [if_neg hw, if_neg (fun h => hw h.symm), mul_zero]
  rw [tsum_congr hrw, ENNReal.tsum_mul_right, tsum_reservoirStep_survival]
  by_cases hw : w = some j
  · rw [if_pos hw, if_pos hw, mul_one]
  · rw [if_neg hw, if_neg hw, mul_zero]

/-- **Reservoir step, new target.** At the `k`-th reservoir step, for any prior winner `w ≠ some k`,
the step lands on the new entry `some k` exactly when the coin hits (`b = 0`), with probability
`1 / (k + 1)` (`probOutput_reservoirStep_win`). -/
lemma probOutput_reservoirStep_eq (k : ℕ) (w : Option ℕ) (hw : w ≠ some k) :
    Pr[= some k | (($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1))) >>= fun b =>
        pure (if b = 0 then some k else w) : ProbComp (Option ℕ))]
      = ((k : ℝ≥0∞) + 1)⁻¹ := by
  rw [probOutput_bind_eq_tsum]
  simp only [probOutput_pure]
  have hrw : ∀ x : Fin (k + 1),
      Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] *
        (if some k = if x = 0 then some k else w then (1 : ℝ≥0∞) else 0)
        = (if x = 0 then Pr[= x | ($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1)))] else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp only [if_true, mul_one]
    · simp only [if_neg hx]
      rw [if_neg (fun h => hw h.symm), mul_zero]
  rw [tsum_congr hrw, tsum_eq_single 0 (fun x hx => by rw [if_neg hx]), if_pos rfl,
    probOutput_uniformSample]
  simp [Fintype.card_fin]

/-- **Reservoir winner index is bounded.** Every winner index in the support of an `n`-step
reservoir run is strictly below `n`: a winner is only ever recorded at an entry that has already
been processed.  This guarantees the prior winner `w` from `reservoirWinnerIndex k` is never the
yet-unseen index `k`, the side condition consumed by `probOutput_reservoirStep_eq`. -/
lemma reservoirWinnerIndex_support_lt :
    ∀ (n : ℕ) (w : Option ℕ), w ∈ support (reservoirWinnerIndex n) →
      ∀ i, w = some i → i < n
  | 0, w, hw, i, hi => by
      simp only [reservoirWinnerIndex, support_pure, Set.mem_singleton_iff] at hw
      rw [hw] at hi; exact absurd hi (by simp)
  | k + 1, w, hw, i, hi => by
      rw [reservoirWinnerIndex_succ] at hw
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
      obtain ⟨w', hw', b, _, hwb⟩ := hw
      by_cases hb0 : b = 0
      · rw [if_pos hb0] at hwb
        rw [hwb] at hi
        have : i = k := Option.some.inj hi.symm
        omega
      · rw [if_neg hb0] at hwb
        rw [hwb] at hi
        exact Nat.lt_succ_of_lt (reservoirWinnerIndex_support_lt k w' hw' i hi)

/-- The pure reservoir winner-index process never fails: it is built from `pure` and the
never-failing uniform coin draws `$ᵗ Fin (k + 1)`. -/
lemma reservoirWinnerIndex_neverFail : ∀ n, NeverFail (reservoirWinnerIndex n)
  | 0 => by rw [reservoirWinnerIndex]; infer_instance
  | k + 1 => by
      rw [reservoirWinnerIndex]
      have := reservoirWinnerIndex_neverFail k
      exact NeverFail.bind_of_forall

/-- The winner marginal of the reservoir process is a genuine distribution: its outputs sum to `1`
(it never fails), so the per-index probabilities partition the unit mass. -/
lemma tsum_probOutput_reservoirWinnerIndex (n : ℕ) :
    ∑' w : Option ℕ, Pr[= w | reservoirWinnerIndex n] = 1 :=
  tsum_probOutput_eq_one' (reservoirWinnerIndex_neverFail n).probFailure_eq_zero

/-- **D2a — reservoir winner uniformity.** After `N` programmed entries, the reservoir winner is
each entry with probability exactly `1 / N`.  The winner marginal depends only on the reservoir
coins `b_k ← $ᵗ Fin (k + 1)` — drawn independently of every cache value — so it is computed purely
by the recursion `reservoirWinnerIndex`; the telescoping of the per-step embedding mass
`1 / (k + 1)` against the survival product `∏ k / (k + 1)` collapses to the uniform `1 / N`. This is
the
data-independent winner-selection core of the GPV Step-2 reservoir close, separable from the
embedding-indistinguishability coupling `hreg`. -/
lemma probOutput_reservoirWinnerIndex_eq :
    ∀ (N j : ℕ), j < N → Pr[= some j | reservoirWinnerIndex N] = (N : ℝ≥0∞)⁻¹
  | 0, j, hj => absurd hj (by omega)
  | k + 1, j, hj => by
      rw [reservoirWinnerIndex_succ, probOutput_bind_eq_tsum]
      by_cases hjk : j = k
      · -- the target is the new entry; every prior winner `w ≠ some j` loses to it
        subst hjk
        have hcongr : ∀ w : Option ℕ,
            Pr[= w | reservoirWinnerIndex j] *
              Pr[= some j | (($ᵗ Fin (j + 1) : ProbComp (Fin (j + 1))) >>= fun b =>
                pure (if b = 0 then some j else w) : ProbComp (Option ℕ))]
              = Pr[= w | reservoirWinnerIndex j] * ((j : ℝ≥0∞) + 1)⁻¹ := by
          intro w
          by_cases hw : w ∈ support (reservoirWinnerIndex j)
          · rw [probOutput_reservoirStep_eq j w (fun hwk =>
              absurd (reservoirWinnerIndex_support_lt j w hw j hwk) (by omega))]
          · rw [probOutput_eq_zero_of_not_mem_support hw, zero_mul, zero_mul]
        rw [tsum_congr hcongr, ENNReal.tsum_mul_right,
          tsum_probOutput_reservoirWinnerIndex, one_mul]
        push_cast; ring_nf
      · -- the target is an earlier entry `j < k`; it must survive (`b ≠ 0`) and already be `w`
        rw [tsum_congr (fun w => by rw [probOutput_reservoirStep_ne k w j hjk] :
          ∀ w : Option ℕ, Pr[= w | reservoirWinnerIndex k] *
              Pr[= some j | (($ᵗ Fin (k + 1) : ProbComp (Fin (k + 1))) >>= fun b =>
                pure (if b = 0 then some k else w) : ProbComp (Option ℕ))]
            = Pr[= w | reservoirWinnerIndex k] *
                (if w = some j then ((k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1)) else 0))]
        rw [tsum_eq_single (some j) (fun w hw => by rw [if_neg (fun h => hw h), mul_zero]),
          if_pos rfl, probOutput_reservoirWinnerIndex_eq k j (by omega)]
        have hk : (k : ℝ≥0∞) ≠ 0 := by
          simp only [ne_eq, Nat.cast_eq_zero]; omega
        rw [ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm ((k : ℝ≥0∞))⁻¹ ((k : ℝ≥0∞) + 1)⁻¹,
          mul_assoc, ENNReal.inv_mul_cancel hk (by simp), mul_one]
        push_cast
        ring_nf

/-- **D2b — the reservoir winner index always lands on a programmed entry.** Starting from at least
one programmed entry, the reservoir winner marginal places no mass on `none`: every run of
`reservoirWinnerIndex (N + 1)` selects one of the recorded slots.  This is the exhaustiveness fact
the in-fold lift consumes: the union of the per-slot winning events `{winner = some j}` exhausts the
winner marginal, so summing the per-slot uniform mass `1 / N` (`probOutput_reservoirWinnerIndex_eq`)
over the `N` slots recovers the whole probability with no leftover `none` branch. Proved by
partitioning the unit total mass (`tsum_probOutput_reservoirWinnerIndex`) into the `none` atom and
the `some j` atoms, the latter summing to `∑_{j < N} 1 / N = 1` by D2a together with the support
bound `reservoirWinnerIndex_support_lt`. -/
lemma probOutput_reservoirWinnerIndex_none_eq_zero (N : ℕ) (hN : N ≠ 0) :
    Pr[= (none : Option ℕ) | reservoirWinnerIndex N] = 0 := by
  have hsplit : ∑' w : Option ℕ, Pr[= w | reservoirWinnerIndex N]
      = Pr[= (none : Option ℕ) | reservoirWinnerIndex N]
        + ∑' j : ℕ, Pr[= some j | reservoirWinnerIndex N] := by
    rw [tsum_option _ ENNReal.summable]
  rw [tsum_probOutput_reservoirWinnerIndex] at hsplit
  have hsome : ∑' j : ℕ, Pr[= some j | reservoirWinnerIndex N] = 1 := by
    have hpt : ∀ j : ℕ,
        Pr[= some j | reservoirWinnerIndex N] = if j < N then (N : ℝ≥0∞)⁻¹ else 0 := by
      intro j
      by_cases hj : j < N
      · rw [if_pos hj, probOutput_reservoirWinnerIndex_eq N j hj]
      · rw [if_neg hj]
        exact probOutput_eq_zero_of_not_mem_support
          (fun hmem => hj (reservoirWinnerIndex_support_lt N (some j) hmem j rfl))
    rw [tsum_congr hpt,
      tsum_eq_sum (s := Finset.range N) (fun j hj => by rw [if_neg]; simpa using hj)]
    rw [Finset.sum_congr rfl (fun j hj => by rw [if_pos (Finset.mem_range.mp hj)])]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (by exact_mod_cast hN) (by simp)]
  rw [hsome] at hsplit
  have h1 : Pr[= (none : Option ℕ) | reservoirWinnerIndex N] + 1 = 0 + 1 := by
    rw [zero_add]; exact hsplit.symm
  exact WithTop.add_right_cancel one_ne_top h1

/-- **D2b — reservoir winner uniform lower bound.** When the realized programmed-entry count `N` is
at most the multi-target budget `Q := qSign + qHash`, the reservoir winner lands on any fixed slot
`j < N` with probability at least `1 / Q`.  This converts the exact per-`N` uniformity of D2a
(`probOutput_reservoirWinnerIndex_eq`, each slot has mass exactly `1 / N`) into the budget-uniform
lower bound `1 / Q` that the multi-target factor `qSign + qHash` of the exact-match reduction pays:
since `N ≤ Q`, `1 / N ≥ 1 / Q`.  Lifting this per-slot bound into the in-fold run (where `N` and the
slot identities are adaptive, but always `N ≤ qSign + qHash` by `combined_run_table_card_le`) is the
data-independent core of the reservoir close. -/
lemma probOutput_reservoirWinnerIndex_ge (N j Q : ℕ) (hj : j < N) (hNQ : N ≤ Q) :
    (Q : ℝ≥0∞)⁻¹ ≤ Pr[= some j | reservoirWinnerIndex N] := by
  rw [probOutput_reservoirWinnerIndex_eq N j hj]
  exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hNQ)

/-- **Pre-sampled-index programmed-preimage reduction.** Draws the embed index up front via
`reservoirWinnerIndex (qSign + qHash)` (uniform over the at-most-`qSign + qHash` programmed entries;
`none` only when there is no budget, mapped to an out-of-range index that never embeds), then runs
the adversary under `embedAtIndexImpl` from the empty state and returns the forged preimage. Unlike
the online reservoir handler, the embed index is fixed before the run, so the simulated random
oracle is consistent under re-query. -/
noncomputable def programmedPreimageReduction
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ) :
    ProgrammedPreimageAdversary (PK := PK) (Domain := Domain) (Range := Range) :=
  fun pk y => do
    let wOpt ← reservoirWinnerIndex (qSign + qHash)
    let ((_msgStar, (_rStar, sStar)), _st) ←
      (simulateQ (embedAtIndexImpl psf M Salt domainSample pk (wOpt.getD (qSign + qHash)) y)
        (adv.main pk)).run ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
    pure sStar

omit [Fintype Salt] in
/-- **The pre-sampled-index reduction, unfolded to its index draw and handler run.** Restates the
reduction body in terms of the named handler `embedAtIndexImpl`: draw the embed index, run the
adversary under the handler from the empty state, and read off the forged preimage. -/
lemma programmedPreimageReduction_eq_run
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ) (pk : PK) (y : Range) :
    programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y =
      (do
        let wOpt ← reservoirWinnerIndex (qSign + qHash)
        let r ← (simulateQ (embedAtIndexImpl psf M Salt domainSample pk
            (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure r.1.2.2) := rfl

omit [Fintype Salt] in
/-- **Advantage of the pre-sampled-index reduction as an averaged exact-match probability.** The
success probability of the reduction in the keyed programmed-preimage game equals the chance,
averaged over a fresh key pair `(pk, sk) ← hr.gen` and a uniform target `y`, that the reduction
reproduces the challenger's hidden short preimage `x`. Exposes the exact-match event as a plain
`Pr[= true | …]` bind so the Step-2 extraction can average it against the same keygen mass. -/
theorem programmedPreimageAdvantage_reduction_eq [DecidableEq Domain]
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain) (qSign qHash : ℕ) :
    programmedPreimageAdvantage (psf := psf) (hr := hr)
        (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash)
      = Pr[= true | (hr.gen >>= fun pksk => (do
          let y ← ($ᵗ Range : ProbComp Range)
          let x ← psf.trapdoorSample pksk.1 pksk.2 y
          let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash
            pksk.1 y
          pure (decide (x' = x))) : ProbComp Bool)] := by
  unfold programmedPreimageAdvantage programmedPreimageExp
  rfl

open Classical in
omit [Fintype Salt] in
/-- **SL-A: the 3-term averaging reduction skeleton.** Reduces the Step-2 keygen-averaged
programmed-game bound to a single per-key `(pk, sk)` bound by expanding all three advantage terms
over the common keygen mass `𝒟[hr.gen]`.  Given a per-key hypothesis `h` bounding the programmed
freshness game at `pk` by the reduction's collision event at `pk` plus the multi-target factor
`qSign + qHash` times the exact-match event at `(pk, sk)`, averaging `h` over `(pk, sk) ← hr.gen`
re-folds the right-hand averages into `collisionFindingAdvantage (reduction …)` (via SL-C, whose
`Prod.fst` keygen pushforward matches the full keygen mass) and `programmedPreimageAdvantage
(programmedPreimageReduction …)` (via its preimage analog). -/
theorem gpv_progGameVerifyFreshAvg_le_of_perKey [DecidableEq Domain]
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (h : ∀ pksk ∈ support hr.gen,
      Pr[= true | progGameVerifyFresh psf hr M Salt adv domainSample pksk.1]
        ≤ Pr[= true | (reduction psf hr M Salt adv domainSample pksk.1 >>= fun xs =>
              pure (decide (xs.1 ≠ xs.2) &&
                decide (psf.eval pksk.1 xs.1 = psf.eval pksk.1 xs.2) &&
                psf.isShort xs.1 && psf.isShort xs.2) : ProbComp Bool)]
          + ((qSign + qHash : ℕ) : ENNReal) *
            Pr[= true | (do
              let y ← ($ᵗ Range : ProbComp Range)
              let x ← psf.trapdoorSample pksk.1 pksk.2 y
              let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash
                pksk.1 y
              pure (decide (x' = x)) : ProbComp Bool)]) :
    Pr[= true | (𝒟[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
        progGameVerifyFresh psf hr M Salt adv domainSample pksk.1]
      ≤ collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample)
        + ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) := by
  classical
  rw [collisionFindingAdvantage_reduction_eq psf hr M Salt adv domainSample,
    programmedPreimageAdvantage_reduction_eq psf hr M Salt adv domainSample qSign qHash,
    bind_map_left]
  rw [probOutput_bind_eq_tsum (𝒟[hr.gen] : SPMF (PK × SK)),
    probOutput_bind_eq_tsum hr.gen, probOutput_bind_eq_tsum hr.gen]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support hr.gen
  · rw [mul_left_comm (↑(qSign + qHash) : ENNReal), ← mul_add]
    exact mul_le_mul' le_rfl (h x hx)
  · have hzero : Pr[= x | hr.gen] = 0 := probOutput_eq_zero_of_not_mem_support hx
    have hzero' : Pr[= x | (𝒟[hr.gen] : SPMF (PK × SK))] = 0 :=
      probOutput_eq_zero_of_not_mem_support (mx := hr.gen) hx
    simp [hzero, hzero']

omit [Fintype Salt] in
/-- **D0 — exact-match advantage as a target-averaged reservoir win.** The per-key exact-match term
of the programmed-preimage reduction expands, over the uniform target draw `y ← $ᵗ Range`, into the
weighted sum of the reduction's exact-match win probability at each fixed target `y`.  This is the
entry point for the reservoir analysis: the inner factor `Pr[= true | …]` is the success
probability of `programmedPreimageReduction … pk y` reproducing the trapdoor preimage `x` of the
fixed embedded target `y`, which the reservoir-sampling argument then bounds. -/
lemma programmedPreimage_perKey_eq_tsum [DecidableEq Domain]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let x ← psf.trapdoorSample pk sk y
        let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
        pure (decide (x' = x)) : ProbComp Bool)]
      = ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
          Pr[= true | (do
            let x ← psf.trapdoorSample pk sk y
            let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
            pure (decide (x' = x)) : ProbComp Bool)] := by
  rw [probOutput_bind_eq_tsum]

open Classical in
omit [Fintype Salt] in
/-- **Exact-match verify-strip (Step-2).** The exact-match winning mass on the combined
*verify-extended* run is bounded by the exact-match event on the combined run of `adv.main pk`
*alone*.  As in the distinct-preimage transfer `gpv_perKey_distinct_le_collision`, the verify
continuation is table-passive on the forced cache hit at the forged point
(`run_combined_verifyKont_of_cache_hit`, the forged point is cached by `hForge`), so the
verify-extended event reduces, support-pointwise, to the corresponding event on the final state of
`adv.main pk`'s combined run: the forged message is fresh, the recomputed verification holds, and
the hidden-preimage table records exactly the forged preimage `s⋆` at the forged point.

This is the exact-match twin of the distinct-branch verify-strip embedded in
`gpv_perKey_distinct_le_collision`; it separates the verify-elimination bookkeeping from the
reservoir coupling, leaving a per-key bound that reads only `adv.main pk`'s combined final state. -/
lemma gpv_perKey_exactMatch_verifyStrip_le
    (domainSample : PK → ProbComp Domain) (pk : PK)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample) :
    Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
            (decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2 |
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
          (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ Pr[fun w : (M × (Salt × Domain)) ×
            ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
              (decide (w.1.1 ∉ w.2.1.1.2) &&
                  (decide (psf.eval pk w.1.2.2 =
                      (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                    psf.isShort w.1.2.2)) = true ∧
                w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
          (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
            (adv.main pk)).run
            ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)] := by
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum_subtype]
  conv_rhs => rw [← bind_pure ((simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
    (adv.main pk)).run ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
      fun _ => none)), probEvent_bind_eq_tsum_subtype]
  refine ENNReal.tsum_le_tsum fun p => ?_
  gcongr
  obtain ⟨⟨out, st⟩, hmem⟩ := p
  obtain ⟨msg, r, s⟩ := out
  have hhit : st.1.1.1 (r, msg) = some ((st.1.1.1 (r, msg)).getD (psf.eval pk s)) := by
    have hcache_ne : st.1.1.1 (r, msg) ≠ none :=
      combined_cache_forge_point_ne_none psf hr M Salt domainSample pk adv hForge
        ((msg, (r, s)), st) hmem
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hcache_ne
    rw [hv, Option.getD_some]
  rw [run_combined_verifyKont_of_cache_hit psf M Salt domainSample pk msg r s
      ((st.1.1.1 (r, msg)).getD (psf.eval pk s)) st hhit, probEvent_pure, probEvent_pure]

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **N2 — embed-index handler counter bound.** Over any adversary computation `oa` making at most
`qS` signing queries and `qH` random-oracle queries, every final state of the pre-sampled-index
embedding run `embedAtIndexImpl … w y` advances the running programming counter `.2` by at most
`qS + qH`: uniform steps and random-oracle cache hits leave it untouched, while each signing step
and each random-oracle miss increments it by one (charged against the residual signing or hash
budget).  Starting from counter `0` this bounds the final counter by `qSign + qHash`, the reservoir
size over which `reservoirWinnerIndex` samples its embedding slot. -/
lemma embedAtIndexImpl_run_count_le (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : (Salt × M →ₒ Range).QueryCache × ℕ) (qS qH : ℕ),
      oa.IsQueryBoundP (· matches .inr _) qS →
      oa.IsQueryBoundP (· matches .inl (.inr _)) qH →
      ∀ z ∈ support ((simulateQ (embedAtIndexImpl psf M Salt domainSample pk w y) oa).run s),
        z.2.2 ≤ s.2 + qS + qH := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s qS qH _ _ z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact le_add_right (Nat.le_add_right _ _)
  | query_bind t mx ih =>
      intro s qS qH hQS hQH z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQS hQH
      obtain ⟨hQS1, hQS2⟩ := hQS
      obtain ⟨hQH1, hQH2⟩ := hQH
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · -- uniform query: counter untouched, both budgets pass through
        rw [embedAtIndexImpl_run_inl_inl, map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = s := (Prod.ext_iff.mp hh).2
        have hpst2 : pst.2 = s.2 := by rw [hps']
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        exact le_trans (ih pv pst qS qH hbS hbH z hz) (by omega)
      · -- random-oracle query: hit leaves the counter fixed, miss increments by one
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqH : 0 < qH := by simpa using hQH1
        rw [embedAtIndexImpl_run_inl_inr] at hps
        cases hq : s.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            have hpst2 : pst.2 = s.2 := by rw [← hpst]
            exact le_trans (ih pv pst qS (qH - 1) hbS hbH z hz) (by omega)
        | none =>
            rw [hq, map_eq_bind_pure_comp] at hps
            obtain ⟨sd, -, hpst⟩ := (mem_support_bind_iff _ _ _).1 hps
            simp only [Function.comp_apply] at hpst
            have hpst2 : pst.2 = s.2 + 1 := by
              have h2 := congrArg (Prod.snd ∘ Prod.snd) hpst
              split_ifs at h2 <;> simpa using h2
            exact le_trans (ih pv pst qS (qH - 1) hbS hbH z hz) (by omega)
      · -- signing query: increments the counter, charged against the signing budget
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqS : 0 < qS := by simpa using hQS1
        rw [embedAtIndexImpl_run_inr] at hps
        obtain ⟨r, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        rw [map_eq_bind_pure_comp] at hps
        obtain ⟨sd, -, hpst⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hpst
        have hpst2 : pst.2 = s.2 + 1 := by
          have h2 := congrArg (Prod.snd ∘ Prod.snd) hpst
          simpa using h2
        exact le_trans (ih pv pst (qS - 1) qH hbS hbH z hz) (by omega)

omit [DecidableEq Range] [SampleableType Range] [Fintype Salt] in
/-- **N2 (corollary) — embed-index counter bounded by the reservoir budget.** From the empty start
state `(∅, 0)`, every final state of the pre-sampled-index embedding run of an adversary `oa`
obeying `signHashQueryBound` has running programming counter at most `qSign + qHash`.  This is the
budget the reservoir winner index `reservoirWinnerIndex (qSign + qHash)` samples over. -/
lemma embedAtIndexImpl_run_count_le_budget (domainSample : PK → ProbComp Domain) (pk : PK)
    (w : ℕ) (y : Range) (qSign qHash : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := β)
      (oa := oa) (qSign := qSign) (qHash := qHash))
    {z : β × ((Salt × M →ₒ Range).QueryCache × ℕ)}
    (hmem : z ∈ support ((simulateQ (embedAtIndexImpl psf M Salt domainSample pk w y) oa).run
      ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)))) :
    z.2.2 ≤ qSign + qHash := by
  have := embedAtIndexImpl_run_count_le psf M Salt domainSample pk w y oa
    ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)) qSign qHash hQ.1 hQ.2 z hmem
  simpa using this

/-! #### N5. Counter-augmented trap run: tagging the forged point's programming index

The trapdoor-recording combined run `progGameRunImplCombinedTrap` carries an *unordered* hidden
preimage table `(Salt × M) → Option Domain`, so it does not expose the *order* in which programmed
entries were written.  To partition the trap mass by the programming index of the forged point we
augment the run with a passive `(idxTable, counter)` instrument: a running `ℕ` counter that
increments by one on every programming event (each random-oracle cache miss and each signing step —
exactly the events that write a fresh preimage-table key), and an insertion-index table
`(Salt × M) → Option ℕ` that records, at each such event, the counter value at the time the key was
first written.  The instrument is never *read* during the run, so it is distributionally passive:
projecting it away recovers `progGameRunImplCombinedTrap` exactly
(`map_run_progGameRunImplCombinedTrapCount_proj`).  The insertion-index table is written in lockstep
with the preimage table (`progGameRunImplCombinedTrapCount_idx_iff_table`), so on every trap-winning
trajectory the forged point — being in the preimage table — has a well-defined recorded insertion
index, which drives the trap-mass index partition `∑' j, g j = trap`. -/

open Classical in
/-- **N5 — the counter-augmented trapdoor-recording combined handler.** Identical to
`progGameRunImplCombinedTrap` on its first state component, but additionally threads a passive
`(idxTable, counter)` instrument: a running `ℕ` programming counter and an insertion-index table
`(Salt × M) → Option ℕ`.  At each programming event (random-oracle miss or signing step) it records
the current counter value into the index table at the freshly written key and increments the
counter; on uniform queries and random-oracle cache hits the instrument is left untouched. -/
noncomputable def progGameRunImplCombinedTrapCount (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)) ProbComp) :=
  fun t => StateT.mk fun s =>
    match t with
    | .inl (.inl q) => do
        let v ← (unifSpec.query q : ProbComp _)
        pure (v, s)
    | .inl (.inr q) =>
        match s.1.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let v ← ($ᵗ Range : ProbComp Range)
            let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
            pure (v,
              ((((s.1.1.1.1.cacheQuery q v, s.1.1.1.2), s.1.1.2),
                fun t' => if t' = q then some x else s.1.2 t'),
                ((fun t' => if t' = q then some s.2.2 else s.2.1 t'), s.2.2 + 1)))
    | .inr msg => do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let v ← ($ᵗ Range : ProbComp Range)
        let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
        pure ((r, x),
          ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
            s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
            fun t' => if t' = (r, msg) then some x else s.1.2 t'),
            ((fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1)))

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrapCount` on a uniform query.** -/
lemma progGameRunImplCombinedTrapCount_run_inl_inl (pk : PK) (sk : SK) (q : unifSpec.Domain)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    (progGameRunImplCombinedTrapCount psf M Salt pk sk (.inl (.inl q))).run s =
      (do let v ← (unifSpec.query q : ProbComp _); pure (v, s)) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrapCount` on a random-oracle query.** -/
lemma progGameRunImplCombinedTrapCount_run_inl_inr (pk : PK) (sk : SK)
    (q : (Salt × M →ₒ Range).Domain)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    (progGameRunImplCombinedTrapCount psf M Salt pk sk (.inl (.inr q))).run s =
      (match s.1.1.1.1 q with
        | some v => pure (v, s)
        | none => do
            let v ← ($ᵗ Range : ProbComp Range)
            let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
            pure (v,
              ((((s.1.1.1.1.cacheQuery q v, s.1.1.1.2), s.1.1.2),
                fun t' => if t' = q then some x else s.1.2 t'),
                ((fun t' => if t' = q then some s.2.2 else s.2.1 t'), s.2.2 + 1)))) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **One-step unfolding of `progGameRunImplCombinedTrapCount` on a signing query.** -/
lemma progGameRunImplCombinedTrapCount_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    (progGameRunImplCombinedTrapCount psf M Salt pk sk (.inr msg)).run s =
      (do
        let r ← ($ᵗ Salt : ProbComp Salt)
        let v ← ($ᵗ Range : ProbComp Range)
        let x ← (psf.trapdoorSample pk sk v : ProbComp Domain)
        pure ((r, x),
          ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
            s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
            fun t' => if t' = (r, msg) then some x else s.1.2 t'),
            ((fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1)))) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 per-query projection.** Dropping the `(idxTable, counter)` instrument from one
`progGameRunImplCombinedTrapCount` query step recovers the corresponding
`progGameRunImplCombinedTrap` step.  This is the per-query hypothesis of the state-projection
transport `map_run_simulateQ_eq_of_query_map_eq`, witnessing that the instrument is passive. -/
lemma progGameRunImplCombinedTrapCount_proj (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    Prod.map id
        (Prod.fst : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
            ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) →
          (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) <$>
        (progGameRunImplCombinedTrapCount psf M Salt pk sk t).run s =
      (progGameRunImplCombinedTrap psf M Salt pk sk t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inl, progGameRunImplCombinedTrap_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inr, progGameRunImplCombinedTrap_run_inl_inr]
          cases s.1.1.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => simp [Prod.map]
  | inr msg =>
      rw [progGameRunImplCombinedTrapCount_run_inr, progGameRunImplCombinedTrap_run_inr]
      simp only [map_bind, map_pure, Prod.map, id_eq]

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 run-level projection (passive augmentation).** Dropping the `(idxTable, counter)`
instrument from the full simulated run of `progGameRunImplCombinedTrapCount` over `oa` recovers the
run of `progGameRunImplCombinedTrap` from the projected start state.  Transports the per-query
`progGameRunImplCombinedTrapCount_proj` through the whole computation via
`map_run_simulateQ_eq_of_query_map_eq`: the instrument is distributionally passive, so the
counter and the insertion-index table do not change the trap event mass. -/
lemma map_run_progGameRunImplCombinedTrapCount_proj (pk : PK) (sk : SK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    Prod.map id
        (Prod.fst : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
            ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) →
          (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) <$>
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s =
      (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) →
      (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
    (progGameRunImplCombinedTrapCount_proj psf M Salt pk sk) oa s

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 lockstep-domain invariant.** Starting from a state whose insertion-index table and hidden
preimage table agree on which keys are recorded, every state reachable in the counter-augmented run
preserves that agreement: a key has a recorded preimage iff it has a recorded insertion index.  The
two tables are written by the *same* conditional update at each programming event (random-oracle
miss or signing step) and are both untouched on uniform queries and cache hits, so the per-key
`isSome` status of the two tables stays in lockstep through the whole adaptive fold.  This is the
support-level fact that lets the trap-mass index partition over recorded insertion indices recover
the full trap mass: every trap-winning trajectory, having its forged point in the preimage table,
has a well-defined recorded forged-point insertion index. -/
lemma progGameRunImplCombinedTrapCount_idx_iff_table (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      (∀ k, s.1.2 k ≠ none ↔ s.2.1 k ≠ none) →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        ∀ k, z.2.1.2 k ≠ none ↔ z.2.2.1 k ≠ none := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
  | query_bind t mx ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · -- uniform query: instrument untouched
        rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        rw [hpst] at hz
        exact ih pv s hs z hz
      · -- random-oracle query: hit keeps both tables, miss writes both keys together
        rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            rw [hpst] at hz
            exact ih pv s hs z hz
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            refine ih pv pst ?_ z hz
            intro k
            rw [hpst]
            by_cases hk : k = mc
            · subst hk; simp
            · simp only [if_neg hk]; exact hs k
      · -- signing query: writes both keys together
        rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        refine ih pv pst ?_ z hz
        intro k
        rw [hpst]
        by_cases hk : k = (r, msg)
        · subst hk; simp
        · simp only [if_neg hk]; exact hs k

/-- **Deterministic `Option ℕ`-index partition of an event.** For a computation `mx`, an event `P`,
and an `Option ℕ`-valued index `idx` that is recorded (`≠ none`) on every positive-probability `P`
outcome, the event mass partitions over the index value: `Pr[P] = ∑' j, Pr[P ∧ idx = some j]`.  The
`some j` atoms tile the event, with the index of each `P`-outcome read off the outcome itself.  This
is the abstract index partition behind the GPV Step-2 trap-mass decomposition `∑' j, g j = trap`. -/
theorem probEvent_eq_tsum_probEvent_index_aux {ι : Type} {m : Type → Type} [Monad m]
    [MonadLiftT m SPMF] (mx : m ι) (P : ι → Prop) (idx : ι → Option ℕ)
    (hidx : ∀ x, Pr[= x | mx] ≠ 0 → P x → idx x ≠ none) :
    Pr[P | mx] = ∑' j : ℕ, Pr[fun x => P x ∧ idx x = some j | mx] := by
  classical
  rw [probEvent_eq_tsum_indicator]
  have hcongr : ∀ j : ℕ,
      Pr[fun x => P x ∧ idx x = some j | mx]
        = ∑' x : ι, {x | P x ∧ idx x = some j}.indicator (Pr[= · | mx]) x := by
    intro j; rw [probEvent_eq_tsum_indicator]
  simp_rw [hcongr]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  by_cases hPx : P x
  · rcases eq_or_ne (Pr[= x | mx]) 0 with hp0 | hp0
    · rw [Set.indicator_apply, if_pos (Set.mem_setOf_eq ▸ hPx), hp0]
      symm
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      refine ENNReal.tsum_eq_zero.mpr fun j => ?_
      by_cases hc : P x ∧ idx x = some j
      · rw [if_pos hc, hp0]
      · rw [if_neg hc]
    · obtain ⟨j₀, hj₀⟩ := Option.ne_none_iff_exists'.mp (hidx x hp0 hPx)
      rw [Set.indicator_of_mem (Set.mem_setOf_eq ▸ hPx)]
      rw [tsum_eq_single j₀]
      · rw [Set.indicator_of_mem (Set.mem_setOf_eq ▸ ⟨hPx, hj₀⟩)]
      · intro j hj
        rw [Set.indicator_of_notMem]
        rintro ⟨-, hjeq⟩
        exact hj (by rw [hj₀] at hjeq; exact (Option.some.inj hjeq).symm)
  · rw [Set.indicator_of_notMem (show x ∉ {x | P x} from hPx)]
    symm
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    refine ENNReal.tsum_eq_zero.mpr fun j => ?_
    rw [if_neg (fun h => hPx h.1)]

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 counter bound.** From any start state, every final state of the counter-augmented trap run
of an adversary `oa` bounded by `(qS, qH)` (signing / hash queries) has its running programming
counter at most `s.counter + qS + qH`: the counter is incremented exactly once per programming event
(random-oracle miss or signing step), each charged against the corresponding query budget; uniform
queries and random-oracle cache hits leave the counter fixed.  This is the trapCount-run dual of
`embedAtIndexImpl_run_count_le`. -/
lemma progGameRunImplCombinedTrapCount_run_count_le (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ)) (qS qH : ℕ),
      oa.IsQueryBoundP (· matches .inr _) qS →
      oa.IsQueryBoundP (· matches .inl (.inr _)) qH →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        z.2.2.2 ≤ s.2.2 + qS + qH := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s qS qH _ _ z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact le_add_right (Nat.le_add_right _ _)
  | query_bind t mx ih =>
      intro s qS qH hQS hQH z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQS hQH
      obtain ⟨hQS1, hQS2⟩ := hQS
      obtain ⟨hQH1, hQH2⟩ := hQH
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · -- uniform query: counter untouched
        rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have := ih pv pst qS qH hbS hbH z hz
        rw [hpst] at this; exact le_trans this (by omega)
      · -- random-oracle query: hit leaves the counter fixed, miss increments by one
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqH : 0 < qH := by simpa using hQH1
        rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            have := ih pv pst qS (qH - 1) hbS hbH z hz
            rw [hpst] at this; exact le_trans this (by omega)
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            have := ih pv pst qS (qH - 1) hbS hbH z hz
            have hc : pst.2.2 = s.2.2 + 1 := by rw [hpst]
            rw [hc] at this; exact le_trans this (by omega)
      · -- signing query: increments the counter
        have hbS := hQS2 pv
        have hbH := hQH2 pv
        simp only [reduceCtorEq, ↓reduceIte] at hbS hbH
        have hqS : 0 < qS := by simpa using hQS1
        rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        have := ih pv pst (qS - 1) qH hbS hbH z hz
        have hc : pst.2.2 = s.2.2 + 1 := by rw [hpst]
        rw [hc] at this; exact le_trans this (by omega)

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 recorded-index range.** From a start state whose insertion-index table only records indices
strictly below the running counter, every state reachable in the counter-augmented trap run
preserves that bound: every recorded insertion index is `< counter`.  Each programming event records
the *current* counter value and then increments the counter, so the freshly recorded index is `<`
the new counter; previously recorded indices stay below the (only larger) counter; uniform queries
and cache hits leave both unchanged. -/
lemma progGameRunImplCombinedTrapCount_idx_lt_count (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ)),
      (∀ k i, s.2.1 k = some i → i < s.2.2) →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        ∀ k i, z.2.2.1 k = some i → i < z.2.2.2 := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
  | query_bind t mx ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · -- uniform query: instrument untouched
        rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        refine ih pv pst ?_ z hz
        rw [hpst]; exact hs
      · -- random-oracle query: hit unchanged, miss records `counter` and increments
        rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            refine ih pv pst ?_ z hz
            rw [hpst]; exact hs
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            refine ih pv pst ?_ z hz
            intro k i hki
            have hcnt : pst.2.2 = s.2.2 + 1 := by rw [hpst]
            have hidx : pst.2.1 = fun t' => if t' = mc then some s.2.2 else s.2.1 t' := by
              rw [hpst]
            rw [hcnt]
            rw [hidx] at hki
            by_cases hk : k = mc
            · subst hk; simp only [if_true] at hki
              rw [Option.some.injEq] at hki; omega
            · simp only [if_neg hk] at hki
              exact Nat.lt_succ_of_lt (hs k i hki)
      · -- signing query: records `counter` and increments
        rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        refine ih pv pst ?_ z hz
        intro k i hki
        have hcnt : pst.2.2 = s.2.2 + 1 := by rw [hpst]
        have hidx : pst.2.1 = fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t' := by
          rw [hpst]
        rw [hcnt]
        rw [hidx] at hki
        by_cases hk : k = (r, msg)
        · subst hk; simp only [if_true] at hki
          rw [Option.some.injEq] at hki; omega
        · simp only [if_neg hk] at hki
          exact Nat.lt_succ_of_lt (hs k i hki)

omit [DecidableEq Range] [Fintype Salt] in
/-- **N5 recorded-index budget.** From the empty/zero start state, every recorded insertion index of
the counter-augmented trap run of an adversary obeying `signHashQueryBound` is `< qSign + qHash`:
the index is `< counter` (`progGameRunImplCombinedTrapCount_idx_lt_count`) and the counter is
`≤ qSign + qHash` (`progGameRunImplCombinedTrapCount_run_count_le`).  This bounds the realized
programming index that the reservoir winner `reservoirWinnerIndex (qSign + qHash)` samples over. -/
lemma progGameRunImplCombinedTrapCount_idx_lt_budget (pk : PK) (sk : SK) (qSign qHash : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (hQ : signHashQueryBound (S' := Salt × Domain) (α := β)
      (oa := oa) (qSign := qSign) (qHash := qHash))
    {z : β × (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
      ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ))}
    (hmem : z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
        (fun _ => none), 0)))
    {k : Salt × M} {i : ℕ} (hki : z.2.2.1 k = some i) : i < qSign + qHash := by
  have hidx := progGameRunImplCombinedTrapCount_idx_lt_count psf M Salt pk sk oa
    (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
      (fun _ => none), 0) (by intro k i hk; simp at hk) z hmem k i hki
  have hcnt := progGameRunImplCombinedTrapCount_run_count_le psf M Salt pk sk oa
    (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
      (fun _ => none), 0) qSign qHash hQ.1 hQ.2 z hmem
  simp only at hcnt
  omega

omit [DecidableEq Range] [Fintype Salt] in
/-- **N4 (scaffold) — off-slot target independence of the trap-sibling embed step.** The embedded
target `y` enters the trap-sibling handler `embedTrapImpl … j y` at *exactly one* query step: the
random-oracle **miss** whose running count equals the winner slot `j`.  Everywhere else — uniform
queries, random-oracle cache hits, off-`j` random-oracle misses (`s.2 ≠ j`), and signing steps — the
per-step run is *literally independent* of `y`, drawing and caching a fresh uniform image (or, on a
hit, returning the cached value) with no reference to `y`.

This is the structural foundation of the GPV Step-2 front-loading commute: it is what lets the
externally-averaged target `y ← $ᵗ Range` be pushed *past* every non-winner step of the
`simulateQ (embedTrapImpl … j y)` fold (each such step commutes with the front draw by
`OracleComp.DeferredSampling.evalDist_bind_comm`), leaving only the single count-`j` miss at which
`y` is consumed — the slot the inline trap winner draw `v⋆ ← $ᵗ Range` must be coupled to. -/
lemma embedTrapImpl_run_step_indep_of_target (pk : PK) (sk : SK) (j : ℕ) (y₁ y₂ : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ)
    (hoff : ∀ q : (Salt × M →ₒ Range).Domain, t = .inl (.inr q) → s.1 q = none → s.2 ≠ j) :
    (embedTrapImpl psf M Salt pk sk j y₁ t).run s =
      (embedTrapImpl psf M Salt pk sk j y₂ t).run s := by
  cases t with
  | inl q =>
      cases q with
      | inl q => rw [embedTrapImpl_run_inl_inl, embedTrapImpl_run_inl_inl]
      | inr q =>
          rw [embedTrapImpl_run_inl_inr, embedTrapImpl_run_inl_inr]
          cases hq : s.1 q with
          | some v => rfl
          | none => simp only [if_neg (hoff q rfl hq)]
  | inr msg => rw [embedTrapImpl_run_inr, embedTrapImpl_run_inr]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Front-draw commute past one trap-sibling embed step (the answer-irrelevant case).** A leading
independent draw `od : ProbComp ρ` feeding a continuation that runs one `embedTrapImpl … j y` step
and then consumes `od`'s value commutes past that step: the step's answer draw and `od` are
independent `ProbComp`s, so they may be drawn in either order (`evalDist_bind_comm`).

This is the distribution-level building block of the GPV Step-2 embed-side front-loading: it is what
lets the externally-averaged target `y ← $ᵗ Range` be pushed *past* each non-winner step of the
`simulateQ (embedTrapImpl … j y)` fold (combined with `embedTrapImpl_run_step_indep_of_target`,
which makes every off-`j` step literally independent of `y`).  It is fully generic in the step
constructor `t`, so it applies uniformly to uniform queries, random-oracle cache hits/misses, and
signing steps; the only `y`-dependent step is the single count-`j` miss at which `y` is consumed. -/
theorem embedTrapImpl_frontDraw_commute {ρ γ : Type} (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (od : ProbComp ρ)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ)
    (k : ρ → (((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t ×
      ((Salt × M →ₒ Range).QueryCache × ℕ)) → ProbComp γ) :
    𝒟[od >>= fun r =>
        (embedTrapImpl psf M Salt pk sk j y t).run s >>= fun pq => k r pq] =
      𝒟[(embedTrapImpl psf M Salt pk sk j y t).run s >>= fun pq =>
        od >>= fun r => k r pq] :=
  OracleComp.DeferredSampling.evalDist_bind_comm od
    ((embedTrapImpl psf M Salt pk sk j y t).run s) (fun r pq => k r pq)

/-- **Inline-fresh sibling of the trap-sibling embed handler.** Identical state `cache × ℕ`,
counter logic, and never-overwrite discipline as `embedTrapImpl`, but the count-`w` random-oracle
miss is *not* special: at *every* random-oracle miss (winner slot or not) it draws a fresh uniform
image `v ← $ᵗ Range`, caches `v`, and returns `v`.  Equivalently, this is `embedTrapImpl … w y` with
the `if st.2 = w` winner branch deleted — a plain lazy random oracle threading a passive programming
counter (with the same trapdoor-recording signing step as `embedTrapImpl`).

The point of this handler is the GPV Step-2 front-loading: averaging `embedTrapImpl … w y` over an
external target draw `y ← $ᵗ Range` *equals* this inline-fresh run distributionally
(`evalDist_frontDraw_embedTrapImpl_eq_embedTrapFresh`), because the count-`w` miss happens at most
once and there caching a front-loaded `y` versus an inline-fresh `v` is the same uniform draw, while
every other step is literally independent of `y` (`embedTrapImpl_run_step_indep_of_target`). -/
noncomputable def embedTrapFreshImpl (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((Salt × M →ₒ Range).QueryCache × ℕ) ProbComp) :=
  let State := (Salt × M →ₒ Range).QueryCache × ℕ
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          set ((st.1.cacheQuery t v, st.2 + 1) : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set ((st.1.cacheQuery (r, msg) c, st.2 + 1) : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshImpl` on a uniform query. -/
lemma embedTrapFreshImpl_run_inl_inl (pk : PK) (sk : SK) (q : unifSpec.Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    (embedTrapFreshImpl psf M Salt pk sk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshImpl` on a random-oracle query. -/
lemma embedTrapFreshImpl_run_inl_inr (pk : PK) (sk : SK) (q : (Salt × M →ₒ Range).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedTrapFreshImpl psf M Salt pk sk (.inl (.inr q))).run s :
        ProbComp (Range × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (match s.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              ((v, (s.1.cacheQuery q v, s.2 + 1)) :
                Range × ((Salt × M →ₒ Range).QueryCache × ℕ)))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapFreshImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply, StateT.run_set, StateT.run_pure]
  | some v =>
      simp [embedTrapFreshImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshImpl` on a signing query. -/
lemma embedTrapFreshImpl_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) :
    ((embedTrapFreshImpl psf M Salt pk sk (.inr msg)).run s :
        ProbComp ((Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), (s.1.cacheQuery (r, msg) c, s.2 + 1)) :
              Domain → (Salt × Domain) × ((Salt × M →ₒ Range).QueryCache × ℕ))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapFreshImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off the winner slot the trap-sibling embed step *is* the inline-fresh step.** Away from the
count-`j` random-oracle miss — i.e. on every uniform query, every random-oracle cache hit, every
off-`j` random-oracle miss (`s.2 ≠ j`), and every signing step — `embedTrapImpl … j y` and
`embedTrapFreshImpl` run *literally identically*: the only place `embedTrapImpl`'s special winner
branch (`if st.2 = j then embed y`) fires is the count-`j` miss, and there both handlers otherwise
draw a fresh uniform and cache it.  This is the per-step bridge through which the front-loading lift
`evalDist_frontDraw_embedTrapImpl_eq_embedTrapFresh` commutes the front target draw past every
non-winner step. -/
lemma embedTrapImpl_run_step_eq_embedTrapFresh (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ)
    (hoff : ∀ q : (Salt × M →ₒ Range).Domain, t = .inl (.inr q) → s.1 q = none → s.2 ≠ j) :
    (embedTrapImpl psf M Salt pk sk j y t).run s =
      (embedTrapFreshImpl psf M Salt pk sk t).run s := by
  cases t with
  | inl q =>
      cases q with
      | inl q => rw [embedTrapImpl_run_inl_inl, embedTrapFreshImpl_run_inl_inl]
      | inr q =>
          rw [embedTrapImpl_run_inl_inr, embedTrapFreshImpl_run_inl_inr]
          cases hq : s.1 q with
          | some v => rfl
          | none => simp only [if_neg (hoff q rfl hq)]
  | inr msg => rw [embedTrapImpl_run_inr, embedTrapFreshImpl_run_inr]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step the trap-sibling embed counter never decreases.** Every output state of one
`embedTrapImpl … j y` query step has running counter `≥` the start counter: uniform queries and
random-oracle cache hits leave it fixed, random-oracle misses and signing steps increment it by one.
This is the monotonicity that keeps a post-winner run (`j < s.2`) forever clear of the winner slot,
so `embedTrapImpl … j y` and `embedTrapFreshImpl` coincide there. -/
lemma embedTrapImpl_run_step_count_le (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ)
    (z : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t ×
      ((Salt × M →ₒ Range).QueryCache × ℕ))
    (hz : z ∈ support ((embedTrapImpl psf M Salt pk sk j y t).run s)) :
    s.2 ≤ z.2.2 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapImpl_run_inl_inl, map_eq_bind_pure_comp] at hz
          obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
          simp only [Function.comp_apply] at hh
          subst hh
          rfl
      | inr q =>
          rw [embedTrapImpl_run_inl_inr] at hz
          cases hq : s.1 q with
          | some v =>
              rw [hq, support_pure, Set.mem_singleton_iff] at hz
              subst hz; rfl
          | none =>
              rw [hq, map_eq_bind_pure_comp] at hz
              obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
              simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hh
              subst hh; split_ifs <;> simp
  | inr msg =>
      rw [embedTrapImpl_run_inr] at hz
      obtain ⟨r, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨c, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [map_eq_bind_pure_comp] at hz
      obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
      simp only [Function.comp_apply] at hh
      subst hh; simp

omit [DecidableEq Range] [Fintype Salt] in
/-- **Post-winner coincidence.** Once the running programming counter has passed the winner slot
(`j < s.2`), the trap-sibling embed handler `embedTrapImpl … j y` and its inline-fresh sibling
`embedTrapFreshImpl` produce *identical* output distributions over any adaptive computation `oa`:
the counter only increases (`embedTrapImpl_run_step_count_le`), so it never returns to `j`, hence
the winner branch never fires and every step agrees (`embedTrapImpl_run_step_eq_embedTrapFresh`).
The external target `y` is irrelevant past the winner. -/
lemma evalDist_run_embedTrapImpl_eq_embedTrapFresh_of_lt (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : (Salt × M →ₒ Range).QueryCache × ℕ), j < s.2 →
      𝒟[(simulateQ (embedTrapImpl psf M Salt pk sk j y) oa).run s] =
        𝒟[(simulateQ (embedTrapFreshImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _; rfl
  | query_bind t ob ih =>
      intro s hs
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      have hstep : (embedTrapImpl psf M Salt pk sk j y t).run s =
          (embedTrapFreshImpl psf M Salt pk sk t).run s :=
        embedTrapImpl_run_step_eq_embedTrapFresh psf M Salt pk sk j y t s
          (fun q _ _ => by omega)
      rw [hstep]
      refine evalDist_bind_congr (fun p hp => ?_)
      have hcount : s.2 ≤ p.2.2 :=
        embedTrapImpl_run_step_count_le psf M Salt pk sk j y t s p (by rw [hstep]; exact hp)
      exact ih p.1 p.2 (by omega)

omit [DecidableEq Range] [Fintype Salt] in
/-- **The GPV Step-2 front-loading lift.** Averaging the trap-sibling embed run over an *external*
target draw `y ← $ᵗ Range` (drawn before the fold) equals the inline-fresh run `embedTrapFreshImpl`
(which draws a fresh uniform at *every* random-oracle miss, including the winner slot), at any start
state `s`:

`𝒟[y ← $ᵗ Range; (simulateQ (embedTrapImpl … j y) oa).run s]`
`  = 𝒟[(simulateQ embedTrapFreshImpl oa).run s]`.

This is the distribution-level front-loading equality the one-step commute
`embedTrapImpl_frontDraw_commute` lifts across the whole adaptive fold.  Proof by induction on `oa`,
threading the start state (hence the running counter):

* **Pre-winner / off-winner step** (the step is not the count-`j` random-oracle miss — uniform
  query, cache hit, off-`j` miss, or signing): the step is literally `y`-independent and equal to
  the inline-fresh step (`embedTrapImpl_run_step_eq_embedTrapFresh`), so the front `y` draw commutes
  past it (`OracleComp.DeferredSampling.evalDist_bind_comm`); the inductive hypothesis rewrites the
  continuation.
* **Winner step** (count-`j` random-oracle miss): the front `y` is the immediately consumed draw —
  `embedTrapImpl … j y` caches and returns `y` while discarding its own fresh draw, so
  `y ← $ᵗ Range; (cache y; return y)` *is* the inline-fresh draw `v ← $ᵗ Range; (cache v; return v)`
  (the discarded draw collapses by `probFailure_uniformSample`).  After this step the counter is
  `j + 1 > j`, so the trap-sibling and inline-fresh continuations coincide
  (`evalDist_run_embedTrapImpl_eq_embedTrapFresh_of_lt`). -/
lemma evalDist_frontDraw_embedTrapImpl_eq_embedTrapFresh [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : (Salt × M →ₒ Range).QueryCache × ℕ),
      𝒟[(($ᵗ Range : ProbComp Range) >>= fun y =>
          (simulateQ (embedTrapImpl psf M Salt pk sk j y) oa).run s)] =
        𝒟[(simulateQ (embedTrapFreshImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s
      simp only [simulateQ_pure, StateT.run_pure]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
        (probFailure_uniformSample Range)]
  | query_bind t ob ih =>
      intro s
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      -- decide whether this step is the winner (count-`j`) random-oracle miss
      by_cases hwin : ∃ q : (Salt × M →ₒ Range).Domain,
          t = .inl (.inr q) ∧ s.1 q = none ∧ s.2 = j
      · -- **Winner step.** Substitute the front `y` for the inline fresh winner draw.
        obtain ⟨q, rfl, hmiss, hcount⟩ := hwin
        -- Unfold both winner steps: `embedTrapImpl` caches/returns `y` (winner branch, `s.2 = j`),
        -- `embedTrapFreshImpl` caches/returns a fresh `v`.
        rw [show (fun y => (embedTrapImpl psf M Salt pk sk j y (.inl (.inr q))).run s >>= fun p =>
                (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (($ᵗ Range : ProbComp Range) >>= fun _ =>
                  (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob y)).run
                    (s.1.cacheQuery q y, s.2 + 1))) from by
          funext y
          rw [embedTrapImpl_run_inl_inr, hmiss, hcount]
          simp only [↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]]
        rw [show ((embedTrapFreshImpl psf M Salt pk sk (.inl (.inr q))).run s >>= fun p =>
                (simulateQ (embedTrapFreshImpl psf M Salt pk sk) (ob p.1)).run p.2)
              = (($ᵗ Range : ProbComp Range) >>= fun v =>
                  (simulateQ (embedTrapFreshImpl psf M Salt pk sk) (ob v)).run
                    (s.1.cacheQuery q v, s.2 + 1)) from by
          rw [embedTrapFreshImpl_run_inl_inr, hmiss]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]]
        -- Drop the discarded inner draw on the left, then apply post-winner coincidence per `y`.
        refine evalDist_bind_congr' _ (fun y => ?_)
        rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
          (probFailure_uniformSample Range)]
        exact evalDist_run_embedTrapImpl_eq_embedTrapFresh_of_lt psf M Salt pk sk j y (ob y)
          (s.1.cacheQuery q y, s.2 + 1) (by omega)
      · -- **Off-winner step.** The step is `y`-independent; commute the front `y` past it.
        push Not at hwin
        have hoff : ∀ q : (Salt × M →ₒ Range).Domain,
            t = .inl (.inr q) → s.1 q = none → s.2 ≠ j := by
          intro q hq hm; exact hwin q hq hm
        -- rewrite the step (for every `y`) to the inline-fresh step
        rw [show (fun y => (embedTrapImpl psf M Salt pk sk j y t).run s >>= fun p =>
                (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (embedTrapFreshImpl psf M Salt pk sk t).run s >>= fun p =>
                (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob p.1)).run p.2) from by
          funext y
          rw [embedTrapImpl_run_step_eq_embedTrapFresh psf M Salt pk sk j y t s hoff]]
        -- commute the front `y` past the now-`y`-free fresh step
        rw [OracleComp.DeferredSampling.evalDist_bind_comm ($ᵗ Range : ProbComp Range)
          ((embedTrapFreshImpl psf M Salt pk sk t).run s)
          (fun y p => (simulateQ (embedTrapImpl psf M Salt pk sk j y) (ob p.1)).run p.2)]
        -- the continuation is the front-loaded run; the inductive hypothesis rewrites it
        refine evalDist_bind_congr' _ (fun p => ?_)
        exact ih p.1 p.2

/-- **Index-augmented trap-sibling embed handler.** Identical to `embedTrapImpl … j y` on its
`cache × ℕ` state component (winner branch `if st.2 = j then embed y` included), but additionally
threads a passive insertion-index table `(Salt × M) → Option ℕ`: at each programming event
(random-oracle miss or signing step) it records the current counter value into the index table at
the freshly written key.  The index table is never *read* during the run, so it is distributionally
passive: projecting it away recovers `embedTrapImpl … j y` exactly (`embedTrapIdxImpl_proj`).

The point of the augmentation is that at the count-`j` winner random-oracle miss the cached image is
`y` *and* the recorded index is `j`: this is the run-only witness that the forged point being the
embedded winner slot (`cache(forged) = some y`) coincides with `idx(forged) = some j`. -/
noncomputable def embedTrapIdxImpl (pk : PK) (sk : SK) (j : ℕ) (y : Range) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) ProbComp) :=
  let State := ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          if st.1.2 = j then
            set (((st.1.1.cacheQuery t y, st.1.2 + 1),
              fun t' => if t' = t then some st.1.2 else st.2 t') : State)
            pure y
          else
            set (((st.1.1.cacheQuery t v, st.1.2 + 1),
              fun t' => if t' = t then some st.1.2 else st.2 t') : State)
            pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set (((st.1.1.cacheQuery (r, msg) c, st.1.2 + 1),
        fun t' => if t' = (r, msg) then some st.1.2 else st.2 t') : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxImpl` on a uniform query. -/
lemma embedTrapIdxImpl_run_inl_inl (pk : PK) (sk : SK) (j : ℕ) (y : Range) (q : unifSpec.Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    (embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxImpl` on a random-oracle query. -/
lemma embedTrapIdxImpl_run_inl_inr (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (q : (Salt × M →ₒ Range).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    ((embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inr q))).run s :
        ProbComp (Range × (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))) =
      (match s.1.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              (if s.1.2 = j then
                  (y, ((s.1.1.cacheQuery q y, s.1.2 + 1),
                    fun t' => if t' = q then some s.1.2 else s.2 t'))
                else
                  (v, ((s.1.1.cacheQuery q v, s.1.2 + 1),
                    fun t' => if t' = q then some s.1.2 else s.2 t')) :
                Range × (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapIdxImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply]
      refine bind_congr fun v => ?_
      split_ifs with hb <;> simp [StateT.run_set]
  | some v =>
      simp [embedTrapIdxImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxImpl` on a signing query. -/
lemma embedTrapIdxImpl_run_inr (pk : PK) (sk : SK) (j : ℕ) (y : Range) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    ((embedTrapIdxImpl psf M Salt pk sk j y (.inr msg)).run s :
        ProbComp ((Salt × Domain) ×
          (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), ((s.1.1.cacheQuery (r, msg) c, s.1.2 + 1),
              fun t' => if t' = (r, msg) then some s.1.2 else s.2 t')) :
              Domain → (Salt × Domain) ×
                (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapIdxImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query passive projection of `embedTrapIdxImpl`.** Dropping the insertion-index table from
one `embedTrapIdxImpl` query step recovers the corresponding `embedTrapImpl … j y` step. -/
lemma embedTrapIdxImpl_proj (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
        (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (embedTrapIdxImpl psf M Salt pk sk j y t).run s =
      (embedTrapImpl psf M Salt pk sk j y t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapIdxImpl_run_inl_inl, embedTrapImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [embedTrapIdxImpl_run_inl_inr, embedTrapImpl_run_inl_inr]
          cases s.1.1 q with
          | none =>
              simp only [Functor.map_map]
              refine congrArg (fun f => f <$> ($ᵗ Range : ProbComp Range)) ?_
              funext v; split_ifs <;> rfl
          | some v => simp [Prod.map]
  | inr msg =>
      rw [embedTrapIdxImpl_run_inr, embedTrapImpl_run_inr]
      simp [Functor.map_map, Prod.map, map_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level passive projection of `embedTrapIdxImpl`.** Dropping the insertion-index table from
the full simulated run of `embedTrapIdxImpl` over `oa` recovers the run of `embedTrapImpl … j y`. -/
lemma map_run_embedTrapIdxImpl_proj (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
        (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s =
      (simulateQ (embedTrapImpl psf M Salt pk sk j y) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
      (Salt × M →ₒ Range).QueryCache × ℕ)
    (embedTrapIdxImpl_proj psf M Salt pk sk j y) oa s

/-- **Index-augmented inline-fresh embed handler.** Identical to `embedTrapFreshImpl` on its
`cache × ℕ` state component, but additionally threads a passive insertion-index table
`(Salt × M) → Option ℕ`: at each programming event (random-oracle miss or signing step) it records
the current counter value into the index table at the freshly written key.  The index table is
never *read* during the run, so it is distributionally passive: projecting it away recovers
`embedTrapFreshImpl` exactly (`embedTrapFreshIdxImpl_proj`).

This is the embed-side mirror of `progGameRunImplCombinedTrapCount`'s index instrument: both record,
at each fresh random-oracle miss, the running counter value into an index table keyed at the missed
point.  It is the run-only bookkeeping that replaces the `y`-reading win literal
`cache(forged) = some y` of `embedTrapImpl` by the run-only predicate `idx(forged) = some j`. -/
noncomputable def embedTrapFreshIdxImpl (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) ProbComp) :=
  let State := ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          set (((st.1.1.cacheQuery t v, st.1.2 + 1),
            fun t' => if t' = t then some st.1.2 else st.2 t') : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set (((st.1.1.cacheQuery (r, msg) c, st.1.2 + 1),
        fun t' => if t' = (r, msg) then some st.1.2 else st.2 t') : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxImpl` on a uniform query. -/
lemma embedTrapFreshIdxImpl_run_inl_inl (pk : PK) (sk : SK) (q : unifSpec.Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    (embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxImpl` on a random-oracle query. -/
lemma embedTrapFreshIdxImpl_run_inl_inr (pk : PK) (sk : SK) (q : (Salt × M →ₒ Range).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    ((embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inr q))).run s :
        ProbComp (Range × (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))) =
      (match s.1.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              ((v, ((s.1.1.cacheQuery q v, s.1.2 + 1),
                fun t' => if t' = q then some s.1.2 else s.2 t')) :
                Range × (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapFreshIdxImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply, StateT.run_set, StateT.run_pure]
  | some v =>
      simp [embedTrapFreshIdxImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxImpl` on a signing query. -/
lemma embedTrapFreshIdxImpl_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    ((embedTrapFreshIdxImpl psf M Salt pk sk (.inr msg)).run s :
        ProbComp ((Salt × Domain) ×
          (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), ((s.1.1.cacheQuery (r, msg) c, s.1.2 + 1),
              fun t' => if t' = (r, msg) then some s.1.2 else s.2 t')) :
              Domain → (Salt × Domain) ×
                (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapFreshIdxImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query passive projection of `embedTrapFreshIdxImpl`.** Dropping the insertion-index table
from one `embedTrapFreshIdxImpl` query step recovers the corresponding `embedTrapFreshImpl` step:
the index table is written by a deterministic update that does not feed the answer draw or the
`cache × ℕ` update, so it is distributionally passive. -/
lemma embedTrapFreshIdxImpl_proj (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
        (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (embedTrapFreshIdxImpl psf M Salt pk sk t).run s =
      (embedTrapFreshImpl psf M Salt pk sk t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapFreshIdxImpl_run_inl_inl, embedTrapFreshImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [embedTrapFreshIdxImpl_run_inl_inr, embedTrapFreshImpl_run_inl_inr]
          cases s.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => simp [Prod.map]
  | inr msg =>
      rw [embedTrapFreshIdxImpl_run_inr, embedTrapFreshImpl_run_inr]
      simp [Functor.map_map, Prod.map, map_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level passive projection of `embedTrapFreshIdxImpl`.** Dropping the insertion-index table
from the full simulated run of `embedTrapFreshIdxImpl` over `oa` recovers the run of
`embedTrapFreshImpl` from the projected start state.  Transports the per-query
`embedTrapFreshIdxImpl_proj` through the whole computation via
`map_run_simulateQ_eq_of_query_map_eq`. -/
lemma map_run_embedTrapFreshIdxImpl_proj (pk : PK) (sk : SK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) :
    Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
        (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) oa).run s =
      (simulateQ (embedTrapFreshImpl psf M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
      (Salt × M →ₒ Range).QueryCache × ℕ)
    (embedTrapFreshIdxImpl_proj psf M Salt pk sk) oa s

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off the winner slot the idx-augmented trap-sibling embed step *is* the idx-augmented
inline-fresh step.** Away from the count-`j` random-oracle miss the special winner branch never
fires, so `embedTrapIdxImpl … j y` and `embedTrapFreshIdxImpl` run identically (the idx-table update
is identical on both sides).  Idx-augmented mirror of `embedTrapImpl_run_step_eq_embedTrapFresh`. -/
lemma embedTrapIdxImpl_run_step_eq_embedTrapFreshIdx (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))
    (hoff : ∀ q : (Salt × M →ₒ Range).Domain, t = .inl (.inr q) → s.1.1 q = none → s.1.2 ≠ j) :
    (embedTrapIdxImpl psf M Salt pk sk j y t).run s =
      (embedTrapFreshIdxImpl psf M Salt pk sk t).run s := by
  cases t with
  | inl q =>
      cases q with
      | inl q => rw [embedTrapIdxImpl_run_inl_inl, embedTrapFreshIdxImpl_run_inl_inl]
      | inr q =>
          rw [embedTrapIdxImpl_run_inl_inr, embedTrapFreshIdxImpl_run_inl_inr]
          cases hq : s.1.1 q with
          | some v => rfl
          | none => simp only [if_neg (hoff q rfl hq)]
  | inr msg => rw [embedTrapIdxImpl_run_inr, embedTrapFreshIdxImpl_run_inr]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step the idx-augmented trap-sibling embed counter never decreases.** Idx-augmented mirror
of `embedTrapImpl_run_step_count_le`. -/
lemma embedTrapIdxImpl_run_step_count_le (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))
    (z : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t ×
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)))
    (hz : z ∈ support ((embedTrapIdxImpl psf M Salt pk sk j y t).run s)) :
    s.1.2 ≤ z.2.1.2 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapIdxImpl_run_inl_inl, map_eq_bind_pure_comp] at hz
          obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
          simp only [Function.comp_apply] at hh
          subst hh
          rfl
      | inr q =>
          rw [embedTrapIdxImpl_run_inl_inr] at hz
          cases hq : s.1.1 q with
          | some v =>
              rw [hq, support_pure, Set.mem_singleton_iff] at hz
              subst hz; rfl
          | none =>
              rw [hq, map_eq_bind_pure_comp] at hz
              obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
              simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hh
              subst hh; split_ifs <;> simp
  | inr msg =>
      rw [embedTrapIdxImpl_run_inr] at hz
      obtain ⟨r, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨c, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [map_eq_bind_pure_comp] at hz
      obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
      simp only [Function.comp_apply] at hh
      subst hh; simp

omit [DecidableEq Range] [Fintype Salt] in
/-- **Post-winner coincidence (idx-augmented).** Once the running counter has passed the winner slot
(`j < s.1.2`), `embedTrapIdxImpl … j y` and `embedTrapFreshIdxImpl` produce identical output
distributions over any `oa`.  Idx-augmented mirror of
`evalDist_run_embedTrapImpl_eq_embedTrapFresh_of_lt`. -/
lemma evalDist_run_embedTrapIdxImpl_eq_embedTrapFreshIdx_of_lt (pk : PK) (sk : SK) (j : ℕ)
    (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)), j < s.1.2 →
      𝒟[(simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s] =
        𝒟[(simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _; rfl
  | query_bind t ob ih =>
      intro s hs
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      have hstep : (embedTrapIdxImpl psf M Salt pk sk j y t).run s =
          (embedTrapFreshIdxImpl psf M Salt pk sk t).run s :=
        embedTrapIdxImpl_run_step_eq_embedTrapFreshIdx psf M Salt pk sk j y t s
          (fun q _ _ => by omega)
      rw [hstep]
      refine evalDist_bind_congr (fun p hp => ?_)
      have hcount : s.1.2 ≤ p.2.1.2 :=
        embedTrapIdxImpl_run_step_count_le psf M Salt pk sk j y t s p (by rw [hstep]; exact hp)
      exact ih p.1 p.2 (by omega)

omit [DecidableEq Range] [Fintype Salt] in
/-- **The idx-augmented GPV Step-2 front-loading lift.** Averaging the idx-augmented trap-sibling
embed run over an external target draw `y ← $ᵗ Range` equals the idx-augmented inline-fresh run
`embedTrapFreshIdxImpl`.  Idx-augmented mirror of
`evalDist_frontDraw_embedTrapImpl_eq_embedTrapFresh`: off-winner steps commute the front `y` past
`y`-independent steps; at the count-`j` winner miss the front `y` is the immediately consumed draw
(cached at the slot tagged `idx = some j`), so the front `y` *is* the inline-fresh winner draw, and
post-winner the two runs coincide (`evalDist_run_embedTrapIdxImpl_eq_embedTrapFreshIdx_of_lt`). -/
lemma evalDist_frontDraw_embedTrapIdxImpl_eq_embedTrapFreshIdx [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)),
      𝒟[(($ᵗ Range : ProbComp Range) >>= fun y =>
          (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s)] =
        𝒟[(simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s
      simp only [simulateQ_pure, StateT.run_pure]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
        (probFailure_uniformSample Range)]
  | query_bind t ob ih =>
      intro s
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      by_cases hwin : ∃ q : (Salt × M →ₒ Range).Domain,
          t = .inl (.inr q) ∧ s.1.1 q = none ∧ s.1.2 = j
      · -- **Winner step.** Substitute the front `y` for the inline fresh winner draw.
        obtain ⟨q, rfl, hmiss, hcount⟩ := hwin
        rw [show (fun y => (embedTrapIdxImpl psf M Salt pk sk j y (.inl (.inr q))).run s >>=
                fun p => (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (($ᵗ Range : ProbComp Range) >>= fun _ =>
                  (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob y)).run
                    ((s.1.1.cacheQuery q y, s.1.2 + 1),
                      fun t' => if t' = q then some s.1.2 else s.2 t'))) from by
          funext y
          rw [embedTrapIdxImpl_run_inl_inr, hmiss, hcount]
          simp only [↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]]
        rw [show ((embedTrapFreshIdxImpl psf M Salt pk sk (.inl (.inr q))).run s >>= fun p =>
                (simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) (ob p.1)).run p.2)
              = (($ᵗ Range : ProbComp Range) >>= fun v =>
                  (simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) (ob v)).run
                    ((s.1.1.cacheQuery q v, s.1.2 + 1),
                      fun t' => if t' = q then some s.1.2 else s.2 t')) from by
          rw [embedTrapFreshIdxImpl_run_inl_inr, hmiss]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]]
        refine evalDist_bind_congr' _ (fun y => ?_)
        rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
          (probFailure_uniformSample Range)]
        exact evalDist_run_embedTrapIdxImpl_eq_embedTrapFreshIdx_of_lt psf M Salt pk sk j y (ob y)
          ((s.1.1.cacheQuery q y, s.1.2 + 1),
            fun t' => if t' = q then some s.1.2 else s.2 t') (by simp only [hcount]; omega)
      · -- **Off-winner step.** The step is `y`-independent; commute the front `y` past it.
        push Not at hwin
        have hoff : ∀ q : (Salt × M →ₒ Range).Domain,
            t = .inl (.inr q) → s.1.1 q = none → s.1.2 ≠ j := by
          intro q hq hm; exact hwin q hq hm
        rw [show (fun y => (embedTrapIdxImpl psf M Salt pk sk j y t).run s >>= fun p =>
                (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (embedTrapFreshIdxImpl psf M Salt pk sk t).run s >>= fun p =>
                (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob p.1)).run p.2) from by
          funext y
          rw [embedTrapIdxImpl_run_step_eq_embedTrapFreshIdx psf M Salt pk sk j y t s hoff]]
        rw [OracleComp.DeferredSampling.evalDist_bind_comm ($ᵗ Range : ProbComp Range)
          ((embedTrapFreshIdxImpl psf M Salt pk sk t).run s)
          (fun y p => (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (ob p.1)).run p.2)]
        refine evalDist_bind_congr' _ (fun p => ?_)
        exact ih p.1 p.2

open Classical in
omit [Fintype Salt] in
/-- **Index-augmented winner-slot restriction of the per-target embedding win is a lower bound.**
Running the embed game on the index-augmented handler `embedTrapIdxImpl … j y` and conjoining the
win predicate with the run-only winner-slot witness `idx(forged) = some j` can only *decrease* the
win mass relative to the un-augmented per-target win on `embedTrapImpl … j y`:

* the index table is passive, so the augmented run projects onto the un-augmented run
  (`map_run_embedTrapIdxImpl_proj`) — the win predicate and the trapdoor draw read only the shared
  output/cache components;
* the extra conjunct `idx(forged) = some j` only restricts the event (`probOutput_bind_mono`).

Averaged over the front target `y ← $ᵗ Range` this gives the winner-slot-restricted lower bound
that the trap-count run's index-tagged trap mass couples to. -/
lemma reservoir_embed_winnerIdx_le [DecidableEq Domain] [Inhabited Range] (pk : PK) (sk : SK)
    (j : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
        Pr[= true | (do
          let r ← (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
            (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))
          let x ← psf.trapdoorSample pk sk ((r.2.1.1 (r.1.2.1, r.1.1)).getD y)
          pure (decide (r.1.2.2 = x) && decide (r.2.1.1 (r.1.2.1, r.1.1) = some y) &&
            decide (r.2.2 (r.1.2.1, r.1.1) = some j)) : ProbComp Bool)]) ≤
      Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk ((r.2.1 (r.1.2.1, r.1.1)).getD y)
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  rw [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun y => ?_
  refine mul_le_mul' le_rfl ?_
  -- Rewrite the un-augmented embed run as the projection of the index-augmented run.
  rw [show (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
        ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
      = Prod.map id (Prod.fst : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ) →
          (Salt × M →ₒ Range).QueryCache × ℕ) <$>
        (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
          (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none)) from
    (map_run_embedTrapIdxImpl_proj psf M Salt pk sk j y (adv.main pk)
      (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))).symm]
  rw [bind_map_left]
  -- Both sides now share the index-augmented run; compare per output `r`.
  refine probOutput_bind_mono (fun r _ => ?_)
  simp only [Prod.map, id_eq]
  -- Per output `r` the trapdoor draws agree; the augmented win adds the conjunct
  -- `idx(forged) = some j`, which can only restrict.
  refine probOutput_bind_mono (fun x _ => ?_)
  simp only [probOutput_pure]
  split_ifs with h1 h2 <;> first | rfl | simp_all

omit [DecidableEq Range] [Fintype Salt] in
/-- **Embed-side index/cache lockstep invariant.** On the index-augmented embed run
`embedTrapIdxImpl … j y`, the cache table and the insertion-index table agree on which keys are
recorded: a key has a cached random-oracle value iff it has a recorded insertion index.  Both tables
are written by the *same* conditional update at each programming event (random-oracle miss or
signing step) and are both untouched on uniform queries and cache hits, so their per-key
`isSome` status stays in lockstep through the whole adaptive fold.  In particular
`idx(forged) = some j` forces
`cache(forged) ≠ none`, which pins the trapdoor draw `trapdoorSample pk sk ((cache forged).getD y)`
to the cached image, eliminating the dependence on the front target `y`. -/
lemma embedTrapIdxImpl_idx_iff_cache (pk : PK) (sk : SK) (j : ℕ) (y : Range) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)),
      (∀ k, s.1.1 k ≠ none ↔ s.2 k ≠ none) →
      ∀ z ∈ support ((simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s),
        ∀ k, z.2.1.1 k ≠ none ↔ z.2.2 k ≠ none := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hs
  | query_bind t mx ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz2⟩
      rcases t with (n | mc) | msg
      · rw [embedTrapIdxImpl_run_inl_inl, map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = s := (Prod.ext_iff.mp hh).2
        refine ih pv pst ?_ z hz2
        rw [hps']; exact hs
      · rw [embedTrapIdxImpl_run_inl_inr] at hps
        cases hq : s.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            refine ih pv pst ?_ z hz2
            rw [hpst]; exact hs
        | none =>
            rw [hq, map_eq_bind_pure_comp] at hps
            obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
            simp only [Function.comp_apply] at hh
            have hps' : pst = ((if s.1.2 = j then s.1.1.cacheQuery mc y
                  else s.1.1.cacheQuery mc v, s.1.2 + 1),
                fun t' => if t' = mc then some s.1.2 else s.2 t') := by
              have h2 := (Prod.ext_iff.mp hh).2
              by_cases hb : s.1.2 = j <;> simp only [hb, if_true, if_false] at h2 ⊢ <;>
                exact h2
            refine ih pv pst ?_ z hz2
            intro k
            rw [hps']
            by_cases hk : k = mc
            · subst hk
              by_cases hb : s.1.2 = j <;> simp [hb, QueryCache.cacheQuery_self]
            · by_cases hb : s.1.2 = j <;>
                simp only [hb, if_true, if_false, if_neg hk,
                  QueryCache.cacheQuery_of_ne _ _ hk] <;> exact hs k
      · rw [embedTrapIdxImpl_run_inr] at hps
        obtain ⟨r, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        obtain ⟨c, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        rw [map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = ((s.1.1.cacheQuery (r, msg) c, s.1.2 + 1),
            fun t' => if t' = (r, msg) then some s.1.2 else s.2 t') := (Prod.ext_iff.mp hh).2
        refine ih pv pst ?_ z hz2
        intro k
        rw [hps']
        by_cases hk : k = (r, msg)
        · subst hk; simp [QueryCache.cacheQuery_self]
        · simp only [if_neg hk, QueryCache.cacheQuery_of_ne _ _ hk]; exact hs k

/-! ### Signed-set-augmented index embed handlers

The index-augmented embed handlers `embedTrapIdxImpl` / `embedTrapFreshIdxImpl` track the
insertion-index table but *not* which messages were signed.  The `…Sig` variants below additionally
thread a passive *signed-set* `Finset M`: the signing branch inserts the queried message, while
random-oracle misses and uniform queries leave it untouched.  The signed set is never *read* during
the run, so it is distributionally passive: projecting it away recovers the un-`Sig` handler exactly
(`map_run_embedTrapIdxSigImpl_proj` / `map_run_embedTrapFreshIdxSigImpl_proj`).  Its purpose is the
GPV Step-2 freshness recovery (`embedTrapIdxSigImpl_fresh_idx_cache_eq`): on a key whose message was
never signed, an `idx = some j` tag forces the cached image to be the embedded target `y`. -/

/-- **Signed-set-augmented index-augmented trap-sibling embed handler.** Identical to
`embedTrapIdxImpl … j y` on its `(cache × ℕ) × idxTable` state component (winner branch
`if st.1.2 = j then embed y` included), but additionally threads a passive signed-set `Finset M`:
the signing branch inserts the queried message; random-oracle misses and uniform queries leave the
signed set unchanged.  The signed set is never *read* during the run, so it is distributionally
passive: projecting it away recovers `embedTrapIdxImpl … j y` exactly
(`embedTrapIdxSigImpl_proj`). -/
noncomputable def embedTrapIdxSigImpl (pk : PK) (sk : SK) (j : ℕ) (y : Range) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
        ProbComp) :=
  let State := (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1.1.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          if st.1.1.2 = j then
            set (((((st.1.1.1.cacheQuery t y, st.1.1.2 + 1),
              fun t' => if t' = t then some st.1.1.2 else st.1.2 t'), st.2)) : State)
            pure y
          else
            set (((((st.1.1.1.cacheQuery t v, st.1.1.2 + 1),
              fun t' => if t' = t then some st.1.1.2 else st.1.2 t'), st.2)) : State)
            pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set (((((st.1.1.1.cacheQuery (r, msg) c, st.1.1.2 + 1),
        fun t' => if t' = (r, msg) then some st.1.1.2 else st.1.2 t'),
        insert msg st.2)) : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxSigImpl` on a uniform query. -/
lemma embedTrapIdxSigImpl_run_inl_inl (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (q : unifSpec.Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    (embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxSigImpl` on a random-oracle query. -/
lemma embedTrapIdxSigImpl_run_inl_inr (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (q : (Salt × M →ₒ Range).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    ((embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inr q))).run s :
        ProbComp (Range ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))) =
      (match s.1.1.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              (if s.1.1.2 = j then
                  (y, (((s.1.1.1.cacheQuery q y, s.1.1.2 + 1),
                    fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2))
                else
                  (v, (((s.1.1.1.cacheQuery q v, s.1.1.2 + 1),
                    fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)) :
                Range ×
                  ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1.1.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapIdxSigImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply]
      refine bind_congr fun v => ?_
      split_ifs with hb <;> simp [StateT.run_set]
  | some v =>
      simp [embedTrapIdxSigImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapIdxSigImpl` on a signing query. -/
lemma embedTrapIdxSigImpl_run_inr (pk : PK) (sk : SK) (j : ℕ) (y : Range) (msg : M)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    ((embedTrapIdxSigImpl psf M Salt pk sk j y (.inr msg)).run s :
        ProbComp ((Salt × Domain) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), (((s.1.1.1.cacheQuery (r, msg) c, s.1.1.2 + 1),
              fun t' => if t' = (r, msg) then some s.1.1.2 else s.1.2 t'), insert msg s.2)) :
              Domain → (Salt × Domain) ×
                ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapIdxSigImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query passive projection of `embedTrapIdxSigImpl`.** Dropping the signed set from one
`embedTrapIdxSigImpl` query step recovers the corresponding `embedTrapIdxImpl … j y` step. -/
lemma embedTrapIdxSigImpl_proj (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    Prod.map id (Prod.fst :
        (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
          ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (embedTrapIdxSigImpl psf M Salt pk sk j y t).run s =
      (embedTrapIdxImpl psf M Salt pk sk j y t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapIdxSigImpl_run_inl_inl, embedTrapIdxImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [embedTrapIdxSigImpl_run_inl_inr, embedTrapIdxImpl_run_inl_inr]
          cases s.1.1.1 q with
          | none =>
              simp only [Functor.map_map]
              refine congrArg (fun f => f <$> ($ᵗ Range : ProbComp Range)) ?_
              funext v; split_ifs <;> rfl
          | some v => simp [Prod.map]
  | inr msg =>
      rw [embedTrapIdxSigImpl_run_inr, embedTrapIdxImpl_run_inr]
      simp [Functor.map_map, Prod.map, map_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level passive projection of `embedTrapIdxSigImpl`.** Dropping the signed set from the full
simulated run of `embedTrapIdxSigImpl` over `oa` recovers the run of `embedTrapIdxImpl … j y`. -/
lemma map_run_embedTrapIdxSigImpl_proj (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    Prod.map id (Prod.fst :
        (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
          ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s =
      (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
      ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))
    (embedTrapIdxSigImpl_proj psf M Salt pk sk j y) oa s

/-- **Signed-set-augmented index-augmented inline-fresh embed handler.** Identical to
`embedTrapFreshIdxImpl` on its `(cache × ℕ) × idxTable` state component, but additionally threads a
passive signed-set `Finset M`: the signing branch inserts the queried message; random-oracle misses
and uniform queries leave the signed set unchanged.  The signed set is never *read* during the run,
so it is distributionally passive: projecting it away recovers `embedTrapFreshIdxImpl` exactly
(`embedTrapFreshIdxSigImpl_proj`). -/
noncomputable def embedTrapFreshIdxSigImpl (pk : PK) (sk : SK) :
    QueryImpl ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      (StateT ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
        ProbComp) :=
  let State := (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M
  let roImpl : QueryImpl (Salt × M →ₒ Range) (StateT State ProbComp) :=
    fun t => do
      let st ← get
      match st.1.1.1 t with
      | some v => pure v
      | none => do
          let v ← ($ᵗ Range : ProbComp Range)
          set (((((st.1.1.1.cacheQuery t v, st.1.1.2 + 1),
            fun t' => if t' = t then some st.1.1.2 else st.1.2 t'), st.2)) : State)
          pure v
  let unifImpl : QueryImpl unifSpec (StateT State ProbComp) :=
    fun t => (unifSpec.query t : ProbComp _)
  let signImpl : QueryImpl (M →ₒ (Salt × Domain)) (StateT State ProbComp) :=
    fun msg => do
      let r ← ($ᵗ Salt : ProbComp Salt)
      let c ← ($ᵗ Range : ProbComp Range)
      let x ← (psf.trapdoorSample pk sk c : ProbComp Domain)
      let st ← get
      set (((((st.1.1.1.cacheQuery (r, msg) c, st.1.1.2 + 1),
        fun t' => if t' = (r, msg) then some st.1.1.2 else st.1.2 t'),
        insert msg st.2)) : State)
      pure (r, x)
  (unifImpl + roImpl) + signImpl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxSigImpl` on a uniform query. -/
lemma embedTrapFreshIdxSigImpl_run_inl_inl (pk : PK) (sk : SK) (q : unifSpec.Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    (embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inl q))).run s =
      (fun v => (v, s)) <$> (unifSpec.query q : ProbComp _) := rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxSigImpl` on a random-oracle query. -/
lemma embedTrapFreshIdxSigImpl_run_inl_inr (pk : PK) (sk : SK) (q : (Salt × M →ₒ Range).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    ((embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inr q))).run s :
        ProbComp (Range ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))) =
      (match s.1.1.1 q with
        | some v => pure (v, s)
        | none =>
            (fun v : Range =>
              ((v, (((s.1.1.1.cacheQuery q v, s.1.1.2 + 1),
                fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)) :
                Range ×
                  ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)))
              <$> ($ᵗ Range : ProbComp Range)) := by
  cases hq : s.1.1.1 q with
  | none =>
      simp only [add_apply_inl, add_apply_inr, embedTrapFreshIdxSigImpl, bind_pure_comp,
        map_eq_bind_pure_comp, bind_assoc, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, pure_bind, hq, StateT.run_monadLift, monadLift_self,
        Function.comp_apply, StateT.run_set, StateT.run_pure]
  | some v =>
      simp [embedTrapFreshIdxSigImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        StateT.run_bind, StateT.run_get, hq]

omit [DecidableEq Range] [Fintype Salt] in
/-- One-step unfolding of `embedTrapFreshIdxSigImpl` on a signing query. -/
lemma embedTrapFreshIdxSigImpl_run_inr (pk : PK) (sk : SK) (msg : M)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    ((embedTrapFreshIdxSigImpl psf M Salt pk sk (.inr msg)).run s :
        ProbComp ((Salt × Domain) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))) =
      (($ᵗ Salt : ProbComp Salt) >>= fun r =>
        ($ᵗ Range : ProbComp Range) >>= fun c =>
          (fun x : Domain =>
            ((r, x), (((s.1.1.1.cacheQuery (r, msg) c, s.1.1.2 + 1),
              fun t' => if t' = (r, msg) then some s.1.1.2 else s.1.2 t'), insert msg s.2)) :
              Domain → (Salt × Domain) ×
                ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))
            <$> (psf.trapdoorSample pk sk c : ProbComp Domain)) := by
  simp only [add_apply_inr, embedTrapFreshIdxSigImpl, bind_pure_comp, map_eq_bind_pure_comp,
    bind_assoc, QueryImpl.add_apply_inr, StateT.run_bind, StateT.run_monadLift, monadLift_self,
    StateT.run_get, Function.comp_apply, pure_bind, StateT.run_set, StateT.run_pure]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query passive projection of `embedTrapFreshIdxSigImpl`.** Dropping the signed set from one
`embedTrapFreshIdxSigImpl` query step recovers the corresponding `embedTrapFreshIdxImpl` step. -/
lemma embedTrapFreshIdxSigImpl_proj (pk : PK) (sk : SK)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    Prod.map id (Prod.fst :
        (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
          ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s =
      (embedTrapFreshIdxImpl psf M Salt pk sk t).run s.1 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapFreshIdxSigImpl_run_inl_inl, embedTrapFreshIdxImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [embedTrapFreshIdxSigImpl_run_inl_inr, embedTrapFreshIdxImpl_run_inl_inr]
          cases s.1.1.1 q with
          | none => simp [map_eq_bind_pure_comp, Prod.map]
          | some v => simp [Prod.map]
  | inr msg =>
      rw [embedTrapFreshIdxSigImpl_run_inr, embedTrapFreshIdxImpl_run_inr]
      simp [Functor.map_map, Prod.map, map_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level passive projection of `embedTrapFreshIdxSigImpl`.** Dropping the signed set from the
full simulated run of `embedTrapFreshIdxSigImpl` over `oa` recovers the run of
`embedTrapFreshIdxImpl` from the projected start state. -/
lemma map_run_embedTrapFreshIdxSigImpl_proj (pk : PK) (sk : SK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) :
    Prod.map id (Prod.fst :
        (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
          ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s =
      (simulateQ (embedTrapFreshIdxImpl psf M Salt pk sk) oa).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _
    (Prod.fst : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
      ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))
    (embedTrapFreshIdxSigImpl_proj psf M Salt pk sk) oa s

omit [DecidableEq Range] [Fintype Salt] in
/-- **Off the winner slot the signed-set-augmented trap-sibling embed step *is* the signed-set
inline-fresh step.** Away from the count-`j` random-oracle miss the special winner branch never
fires, so `embedTrapIdxSigImpl … j y` and `embedTrapFreshIdxSigImpl` run identically (the idx-table
and signed-set updates are identical on both sides).  Signed-set mirror of
`embedTrapIdxImpl_run_step_eq_embedTrapFreshIdx`. -/
lemma embedTrapIdxSigImpl_run_step_eq_embedTrapFreshIdxSig (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
    (hoff : ∀ q : (Salt × M →ₒ Range).Domain, t = .inl (.inr q) → s.1.1.1 q = none → s.1.1.2 ≠ j) :
    (embedTrapIdxSigImpl psf M Salt pk sk j y t).run s =
      (embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s := by
  cases t with
  | inl q =>
      cases q with
      | inl q => rw [embedTrapIdxSigImpl_run_inl_inl, embedTrapFreshIdxSigImpl_run_inl_inl]
      | inr q =>
          rw [embedTrapIdxSigImpl_run_inl_inr, embedTrapFreshIdxSigImpl_run_inl_inr]
          cases hq : s.1.1.1 q with
          | some v => rfl
          | none => simp only [if_neg (hoff q rfl hq)]
  | inr msg => rw [embedTrapIdxSigImpl_run_inr, embedTrapFreshIdxSigImpl_run_inr]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step the signed-set-augmented trap-sibling embed counter never decreases.** Signed-set
mirror of `embedTrapIdxImpl_run_step_count_le`. -/
lemma embedTrapIdxSigImpl_run_step_count_le (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
    (z : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range t ×
      ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))
    (hz : z ∈ support ((embedTrapIdxSigImpl psf M Salt pk sk j y t).run s)) :
    s.1.1.2 ≤ z.2.1.1.2 := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [embedTrapIdxSigImpl_run_inl_inl, map_eq_bind_pure_comp] at hz
          obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
          simp only [Function.comp_apply] at hh
          subst hh
          rfl
      | inr q =>
          rw [embedTrapIdxSigImpl_run_inl_inr] at hz
          cases hq : s.1.1.1 q with
          | some v =>
              rw [hq, support_pure, Set.mem_singleton_iff] at hz
              subst hz; rfl
          | none =>
              rw [hq, map_eq_bind_pure_comp] at hz
              obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
              simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hh
              subst hh; split_ifs <;> simp
  | inr msg =>
      rw [embedTrapIdxSigImpl_run_inr] at hz
      obtain ⟨r, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      obtain ⟨c, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [map_eq_bind_pure_comp] at hz
      obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hz
      simp only [Function.comp_apply] at hh
      subst hh; simp

omit [DecidableEq Range] [Fintype Salt] in
/-- **Post-winner coincidence (signed-set-augmented).** Once the running counter has passed the
winner slot (`j < s.1.1.2`), `embedTrapIdxSigImpl … j y` and `embedTrapFreshIdxSigImpl` produce
identical output distributions over any `oa`.  Signed-set mirror of
`evalDist_run_embedTrapIdxImpl_eq_embedTrapFreshIdx_of_lt`. -/
lemma evalDist_run_embedTrapIdxSigImpl_eq_embedTrapFreshIdxSig_of_lt (pk : PK) (sk : SK) (j : ℕ)
    (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
      j < s.1.1.2 →
      𝒟[(simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s] =
        𝒟[(simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _; rfl
  | query_bind t ob ih =>
      intro s hs
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      have hstep : (embedTrapIdxSigImpl psf M Salt pk sk j y t).run s =
          (embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s :=
        embedTrapIdxSigImpl_run_step_eq_embedTrapFreshIdxSig psf M Salt pk sk j y t s
          (fun q _ _ => by omega)
      rw [hstep]
      refine evalDist_bind_congr (fun p hp => ?_)
      have hcount : s.1.1.2 ≤ p.2.1.1.2 :=
        embedTrapIdxSigImpl_run_step_count_le psf M Salt pk sk j y t s p (by rw [hstep]; exact hp)
      exact ih p.1 p.2 (by omega)

omit [DecidableEq Range] [Fintype Salt] in
/-- **The signed-set-augmented GPV Step-2 front-loading lift.** Averaging the signed-set-augmented
trap-sibling embed run over an external target draw `y ← $ᵗ Range` equals the signed-set-augmented
inline-fresh run `embedTrapFreshIdxSigImpl`.  Signed-set mirror of
`evalDist_frontDraw_embedTrapIdxImpl_eq_embedTrapFreshIdx`: off-winner steps commute the front `y`
past `y`-independent steps; at the count-`j` winner miss the front `y` is the immediately consumed
draw, so the front `y` *is* the inline-fresh winner draw, and post-winner the two runs coincide
(`evalDist_run_embedTrapIdxSigImpl_eq_embedTrapFreshIdxSig_of_lt`).  The signed set is updated
identically on both sides (signing ignores `y`) and is never read, so it rides along passively. -/
lemma evalDist_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β) :
    ∀ (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
      𝒟[(($ᵗ Range : ProbComp Range) >>= fun y =>
          (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s)] =
        𝒟[(simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s] := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s
      simp only [simulateQ_pure, StateT.run_pure]
      rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
        (probFailure_uniformSample Range)]
  | query_bind t ob ih =>
      intro s
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      by_cases hwin : ∃ q : (Salt × M →ₒ Range).Domain,
          t = .inl (.inr q) ∧ s.1.1.1 q = none ∧ s.1.1.2 = j
      · -- **Winner step.** Substitute the front `y` for the inline fresh winner draw.
        obtain ⟨q, rfl, hmiss, hcount⟩ := hwin
        rw [show (fun y => (embedTrapIdxSigImpl psf M Salt pk sk j y (.inl (.inr q))).run s >>=
                fun p => (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (($ᵗ Range : ProbComp Range) >>= fun _ =>
                  (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob y)).run
                    (((s.1.1.1.cacheQuery q y, s.1.1.2 + 1),
                      fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2))) from by
          funext y
          rw [embedTrapIdxSigImpl_run_inl_inr, hmiss, hcount]
          simp only [↓reduceIte, map_eq_bind_pure_comp, bind_assoc, pure_bind,
            Function.comp_apply]]
        rw [show ((embedTrapFreshIdxSigImpl psf M Salt pk sk (.inl (.inr q))).run s >>= fun p =>
                (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (ob p.1)).run p.2)
              = (($ᵗ Range : ProbComp Range) >>= fun v =>
                  (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (ob v)).run
                    (((s.1.1.1.cacheQuery q v, s.1.1.2 + 1),
                      fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)) from by
          rw [embedTrapFreshIdxSigImpl_run_inl_inr, hmiss]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]]
        refine evalDist_bind_congr' _ (fun y => ?_)
        rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
          (probFailure_uniformSample Range)]
        exact evalDist_run_embedTrapIdxSigImpl_eq_embedTrapFreshIdxSig_of_lt psf M Salt pk sk j y
          (ob y)
          (((s.1.1.1.cacheQuery q y, s.1.1.2 + 1),
            fun t' => if t' = q then some s.1.1.2 else s.1.2 t'), s.2)
          (by simp only [hcount]; omega)
      · -- **Off-winner step.** The step is `y`-independent; commute the front `y` past it.
        push Not at hwin
        have hoff : ∀ q : (Salt × M →ₒ Range).Domain,
            t = .inl (.inr q) → s.1.1.1 q = none → s.1.1.2 ≠ j := by
          intro q hq hm; exact hwin q hq hm
        rw [show (fun y => (embedTrapIdxSigImpl psf M Salt pk sk j y t).run s >>= fun p =>
                (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob p.1)).run p.2)
              = (fun y => (embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s >>= fun p =>
                (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob p.1)).run p.2) from by
          funext y
          rw [embedTrapIdxSigImpl_run_step_eq_embedTrapFreshIdxSig psf M Salt pk sk j y t s hoff]]
        rw [OracleComp.DeferredSampling.evalDist_bind_comm ($ᵗ Range : ProbComp Range)
          ((embedTrapFreshIdxSigImpl psf M Salt pk sk t).run s)
          (fun y p => (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (ob p.1)).run p.2)]
        refine evalDist_bind_congr' _ (fun p => ?_)
        exact ih p.1 p.2

omit [DecidableEq Range] [Fintype Salt] in
/-- **Expected-functional form of the signed-set front-loading lift.**  For any nonnegative output
functional `F`, the inline-fresh run's expectation equals the front-target-averaged trap-sibling
run's expectation: `∑' w, Pr[= w | freshSig run] · F w = ∑' y, Pr[= y] · ∑' w, Pr[= w |
embedTrapIdxSig … j y run] · F w`.  Immediate from
`evalDist_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl` (the two `evalDist`s agree, so
their expectations of `F` agree) and the Tonelli rearrangement `tsum_probOutput_bind_mul`. -/
lemma tsum_probOutput_embedTrapFreshIdxSig_mul_eq_frontDraw [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
    (F : β × ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) →
      ℝ≥0∞) :
    (∑' w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s] * F w) =
      ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
        ∑' w, Pr[= w | (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s] * F w := by
  have hlift := evalDist_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl psf M Salt pk sk j
    oa s
  have hF : ∀ w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s] =
      Pr[= w | (($ᵗ Range : ProbComp Range) >>= fun y =>
        (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s)] :=
    fun w => by rw [probOutput, probOutput, hlift]
  simp_rw [hF]
  rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Freshness-confined winner-slot cache invariant (state-general form).** On the
signed-set-augmented embed run `embedTrapIdxSigImpl … j y`, the following invariant is preserved
through the whole adaptive fold: for every key `k`, if its recorded insertion index is the winner
index `j` *and* its message was never signed (`k.2 ∉ signedSet`), then its cached random-oracle
image is exactly the embedded target `y`.

The invariant holds because the only programming event that can record `idx k = some j` at an
unsigned key `k` is a *random-oracle miss* at counter value `j` — and the embed handler's count-`j`
winner branch caches exactly `y` there.  The signing branch records its key `(r, msg)` but
simultaneously inserts `msg` into the signed set, so any key it touches has `k.2 ∈ signedSet`
afterwards, falling outside the invariant's unsigned hypothesis.  All other steps (uniform queries,
cache hits, off-`j` misses) either leave the state untouched or record an index `≠ j`. -/
lemma embedTrapIdxSigImpl_fresh_idx_cache_eq_general (pk : PK) (sk : SK) (j : ℕ) (y : Range) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
      (∀ k, s.1.2 k = some j → k.2 ∉ s.2 → s.1.1.1 k = some y) →
      ∀ z ∈ support ((simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run s),
        ∀ k, z.2.1.2 k = some j → k.2 ∉ z.2.2 → z.2.1.1.1 k = some y := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hs
  | query_bind t mx ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz2⟩
      rcases t with (n | mc) | msg
      · rw [embedTrapIdxSigImpl_run_inl_inl, map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = s := (Prod.ext_iff.mp hh).2
        refine ih pv pst ?_ z hz2
        rw [hps']; exact hs
      · rw [embedTrapIdxSigImpl_run_inl_inr] at hps
        cases hq : s.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            refine ih pv pst ?_ z hz2
            rw [hpst]; exact hs
        | none =>
            rw [hq, map_eq_bind_pure_comp] at hps
            obtain ⟨v, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
            simp only [Function.comp_apply] at hh
            have hps' : pst = (((if s.1.1.2 = j then s.1.1.1.cacheQuery mc y
                  else s.1.1.1.cacheQuery mc v, s.1.1.2 + 1),
                fun t' => if t' = mc then some s.1.1.2 else s.1.2 t'), s.2) := by
              have h2 := (Prod.ext_iff.mp hh).2
              by_cases hb : s.1.1.2 = j <;> simp only [hb, if_true, if_false] at h2 ⊢ <;>
                exact h2
            refine ih pv pst ?_ z hz2
            intro k hidx hfresh
            subst hps'
            simp only at hidx hfresh ⊢
            by_cases hk : k = mc
            · subst hk
              -- The miss at `mc` records `idx mc = some s.1.1.2`; the hypothesis forces it `= j`,
              -- so the winner branch fired and cached `y`.
              simp only [if_true, Option.some.injEq] at hidx
              subst hidx
              simp only [if_true, QueryCache.cacheQuery_self]
            · -- Off the missed key the state is the old one; apply `hs`.
              simp only [if_neg hk] at hidx
              by_cases hb : s.1.1.2 = j <;>
                simp only [hb, if_true, if_false, QueryCache.cacheQuery_of_ne _ _ hk] <;>
                exact hs k hidx hfresh
      · rw [embedTrapIdxSigImpl_run_inr] at hps
        obtain ⟨r, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        obtain ⟨c, -, hps⟩ := (mem_support_bind_iff _ _ _).1 hps
        rw [map_eq_bind_pure_comp] at hps
        obtain ⟨x, -, hh⟩ := (mem_support_bind_iff _ _ _).1 hps
        simp only [Function.comp_apply] at hh
        have hps' : pst = (((s.1.1.1.cacheQuery (r, msg) c, s.1.1.2 + 1),
            fun t' => if t' = (r, msg) then some s.1.1.2 else s.1.2 t'),
            insert msg s.2) := (Prod.ext_iff.mp hh).2
        refine ih pv pst ?_ z hz2
        intro k hidx hfresh
        subst hps'
        simp only [Finset.mem_insert, not_or] at hfresh
        obtain ⟨hne, hfresh'⟩ := hfresh
        -- `k.2 ≠ msg` forces `k ≠ (r, msg)`, so the signing step left `idx k` and `cache k` alone.
        have hk : k ≠ (r, msg) := fun hkeq => hne (by rw [hkeq])
        simp only at hidx ⊢
        simp only [if_neg hk] at hidx
        rw [QueryCache.cacheQuery_of_ne _ _ hk]
        exact hs k hidx hfresh'

omit [DecidableEq Range] [Fintype Salt] in
/-- **Freshness-confined winner-slot cache recovery.** On the signed-set-augmented embed run
`embedTrapIdxSigImpl … j y` started from the empty state, any reachable final state `z` satisfies:
for a forged key `k` whose message was never signed (`k.2 ∉ z.signedSet`, the run-only freshness
witness) and whose recorded insertion index is the winner index `j` (`z.idxTable k = some j`), the
cached random-oracle image at `k` is exactly the embedded target `y` (`z.cache k = some y`).

This is the load-bearing freshness recovery for GPV Step-2: freshness rules out the signing branch
(which always signs its key's message), so the only programming event that could have recorded
`idx k = some j` is a count-`j` random-oracle miss, where the embed handler caches exactly `y`.  It
eliminates the free `y` from the embed win literal `cache(forged) = some y` on the winner slot,
specializing `embedTrapIdxSigImpl_fresh_idx_cache_eq_general` to the empty start (vacuous
invariant). -/
lemma embedTrapIdxSigImpl_fresh_idx_cache_eq (pk : PK) (sk : SK) (j : ℕ) (y : Range)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (z : β × ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M))
    (hz : z ∈ support ((simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) oa).run
      ((((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none)),
        (∅ : Finset M)))) :
    ∀ k, z.2.1.2 k = some j → k.2 ∉ z.2.2 → z.2.1.1.1 k = some y :=
  embedTrapIdxSigImpl_fresh_idx_cache_eq_general psf M Salt pk sk j y oa
    ((((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none)), (∅ : Finset M))
    (fun k hidx _ => by simp at hidx) z hz

omit [DecidableEq Range] [Fintype Salt] in
/-- **Write-only trapdoor-table support invariant.** On the counter-augmented trapdoor-recording run
`progGameRunImplCombinedTrapCount`, every recorded preimage is a trapdoor sample of the matching
cached random-oracle image: if `table(k) = some x` then there is a cached value `v` with
`cache(k) = some v` and `x ∈ support (trapdoorSample pk sk v)`.  Each programming event
(random-oracle miss or signing step) caches a fresh image `v` and records `trapdoorSample pk sk v`
into the table at the *same* key in lockstep; the table is never read during the run, so this
`(cache, table)`
agreement is preserved through the whole adaptive fold.  This is the support-level fact behind the
write-only-table deferral matching the trap event `table(forged) = output` to the embed event
`output = trapdoorSample (cache forged)`. -/
lemma progGameRunImplCombinedTrapCount_table_support (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      (∀ k x, s.1.2 k = some x →
        ∃ v, s.1.1.1.1 k = some v ∧ x ∈ support (psf.trapdoorSample pk sk v)) →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        ∀ k x, z.2.1.2 k = some x →
          ∃ v, z.2.1.1.1.1 k = some v ∧ x ∈ support (psf.trapdoorSample pk sk v) := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hs
  | query_bind t mx ih =>
      intro s hs z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        rw [hpst] at hz
        exact ih pv s hs z hz
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            rw [hpst] at hz
            exact ih pv s hs z hz
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, hv, x, hx, -, hpst⟩ := hps
            refine ih pv pst ?_ z hz
            intro k x' hkx'
            have hcache : pst.1.1.1.1 = s.1.1.1.1.cacheQuery mc v := by rw [hpst]
            have htbl : pst.1.2 = fun t' => if t' = mc then some x else s.1.2 t' := by rw [hpst]
            rw [htbl] at hkx'
            rw [hcache]
            by_cases hk : k = mc
            · subst hk
              simp only [if_true] at hkx'
              rw [Option.some.injEq] at hkx'
              subst hkx'
              exact ⟨v, QueryCache.cacheQuery_self _ _ _, hx⟩
            · simp only [if_neg hk] at hkx'
              obtain ⟨w, hw1, hw2⟩ := hs k x' hkx'
              exact ⟨w, by rw [QueryCache.cacheQuery_of_ne _ _ hk]; exact hw1, hw2⟩
      · rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, hx, -, hpst⟩ := hps
        refine ih pv pst ?_ z hz
        intro k x' hkx'
        have hcache : pst.1.1.1.1 = s.1.1.1.1.cacheQuery (r, msg) v := by rw [hpst]
        have htbl : pst.1.2 = fun t' => if t' = (r, msg) then some x else s.1.2 t' := by rw [hpst]
        rw [htbl] at hkx'
        rw [hcache]
        by_cases hk : k = (r, msg)
        · subst hk
          simp only [if_true] at hkx'
          rw [Option.some.injEq] at hkx'
          subst hkx'
          exact ⟨v, QueryCache.cacheQuery_self _ _ _, hx⟩
        · simp only [if_neg hk] at hkx'
          obtain ⟨w, hw1, hw2⟩ := hs k x' hkx'
          exact ⟨w, by rw [QueryCache.cacheQuery_of_ne _ _ hk]; exact hw1, hw2⟩

/-! ### Trap-count → fresh-sig cache/counter/idx/signedSet projection

The counter-augmented trapdoor-recording run `progGameRunImplCombinedTrapCount` and the
signed-set-augmented inline-fresh embed run `embedTrapFreshIdxSigImpl` draw their cached
random-oracle images identically: both cache a *fresh* uniform draw at every programming event (the
trap handler embeds nothing, and the fresh-sig handler has no winner branch).  They differ only in
the *extra* book-keeping the trap run carries — the freshness Bool flag and the write-only trapdoor
preimage table — both of which are distributionally passive.  Dropping them and reshaping the tuple
recovers the fresh-sig run's `(((cache × counter) × idx) × signedSet)` state exactly
(`map_run_progGameRunImplCombinedTrapCount_freshSig_proj`), at the *distribution* level: the trap
run's per-programming-event trapdoor draw `x ← trapdoorSample pk sk v` is never read by either run,
so under `NeverFail` it contributes only its (unit) mass. -/

/-- **`evalDist`-level state-projection transport (differing state types).** If every oracle step of
`impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec'))` becomes the corresponding `impl₂` step after
mapping the state with `proj : σ₁ → σ₂` *at the distribution level*, then the full simulated runs
agree under the same projection at the distribution level.  This is the `evalDist`-level relaxation
of `OracleComp.map_run_simulateQ_eq_of_query_map_eq`: the per-query hypothesis may discard a
never-failing answer-irrelevant draw (e.g. a write-only trapdoor sample) that breaks the *monadic*
equality but preserves the distribution. -/
theorem evalDist_map_run_simulateQ_eq_of_query_evalDist_map_eq
    {ι : Type} {spec : OracleSpec ι}
    {σ₁ σ₂ : Type} {α : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (proj : σ₁ → σ₂)
    (hproj : ∀ t s,
      𝒟[Prod.map id proj <$> (impl₁ t).run s] = 𝒟[(impl₂ t).run (proj s)])
    (oa : OracleComp spec α) (s : σ₁) :
    𝒟[Prod.map id proj <$> (simulateQ impl₁ oa).run s] =
      𝒟[(simulateQ impl₂ oa).run (proj s)] := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind, map_bind]
      rw [evalDist_bind_congr' ((impl₁ t).run s)
        (ob₂ := fun x => (simulateQ impl₂ (oa x.1)).run (proj x.2))
        (fun x => ih x.1 x.2)]
      rw [show ((impl₁ t).run s >>= fun x => (simulateQ impl₂ (oa x.1)).run (proj x.2))
            = ((Prod.map id proj <$> (impl₁ t).run s) >>= fun x =>
                (simulateQ impl₂ (oa x.1)).run x.2) from by
        rw [bind_map_left]; rfl]
      rw [evalDist_bind, hproj t s, ← evalDist_bind]

omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-query trap-count → fresh-sig distribution projection.** Dropping the freshness Bool flag
and the write-only trapdoor table from one `progGameRunImplCombinedTrapCount` query step — and
reshaping the remaining `(cache, signedSet, idx, counter)` components into the fresh-sig
`(((cache × counter) × idx) × signedSet)` layout — recovers the corresponding
`embedTrapFreshIdxSigImpl` step at the distribution level.  Both handlers cache a fresh uniform draw
at every programming event; the trap run's extra trapdoor sample `x ← trapdoorSample pk sk v` is
never read, so under `hNF` it is a never-failing value-irrelevant prefix that drops out. -/
lemma progGameRunImplCombinedTrapCount_freshSig_proj (pk : PK) (sk : SK)
    (hNF : ∀ c : Range, NeverFail (psf.trapdoorSample pk sk c))
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    𝒟[Prod.map id
        (fun s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
              ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) =>
          ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2) :
            (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)) <$>
        (progGameRunImplCombinedTrapCount psf M Salt pk sk t).run s] =
      𝒟[(embedTrapFreshIdxSigImpl psf M Salt pk sk t).run
        ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2))] := by
  cases t with
  | inl q =>
      cases q with
      | inl q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inl, embedTrapFreshIdxSigImpl_run_inl_inl]
          simp [map_eq_bind_pure_comp, Prod.map]
      | inr q =>
          rw [progGameRunImplCombinedTrapCount_run_inl_inr, embedTrapFreshIdxSigImpl_run_inl_inr]
          cases hq : s.1.1.1.1 q with
          | none =>
              -- RO miss: the trapdoor sample `x` is recorded write-only in the table (which the
              -- projection drops), so the projected output is `x`-independent and `x` drops out.
              simp only [map_bind, map_pure, Prod.map, id_eq]
              refine evalDist_bind_congr' _ (fun v => ?_)
              rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails
                (psf.trapdoorSample pk sk v) (hNF v).probFailure_eq_zero _]
              rfl
          | some v => simp [Prod.map]
  | inr msg =>
      -- Signing: the trapdoor sample `x` *is* part of the output `(r, x)` on both sides, so the two
      -- signing steps draw `x ← trapdoorSample pk sk c` and output `(r, x)` identically.
      rw [progGameRunImplCombinedTrapCount_run_inr, embedTrapFreshIdxSigImpl_run_inr]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, Prod.map, id_eq, pure_bind]
      rfl

omit [DecidableEq Range] [Fintype Salt] in
/-- **Run-level trap-count → fresh-sig distribution projection.** Transports the per-query step
`progGameRunImplCombinedTrapCount_freshSig_proj` through the whole adaptive fold via
`evalDist_map_run_simulateQ_eq_of_query_evalDist_map_eq`: dropping the freshness Bool flag and the
write-only trapdoor table from the full simulated trap-count run, and reshaping to the fresh-sig
state layout, recovers the `embedTrapFreshIdxSigImpl` run distribution. -/
lemma map_run_progGameRunImplCombinedTrapCount_freshSig_proj (pk : PK) (sk : SK)
    (hNF : ∀ c : Range, NeverFail (psf.trapdoorSample pk sk c))
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) :
    𝒟[Prod.map id
        (fun s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
              ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) =>
          ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2) :
            (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)) <$>
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] =
      𝒟[(simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run
        ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2))] := by
  exact evalDist_map_run_simulateQ_eq_of_query_evalDist_map_eq
    (progGameRunImplCombinedTrapCount psf M Salt pk sk)
    (embedTrapFreshIdxSigImpl psf M Salt pk sk)
    (fun s => ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2)))
    (progGameRunImplCombinedTrapCount_freshSig_proj psf M Salt pk sk hNF) oa s

omit [Fintype Salt] in
/-- **Step-2 embed-side reduction to the common freshness-confined deferred functional.**  The
inline-fresh-run expectation of the *freshness-confined winner-slot deferred-trapdoor* functional

  `Wf w := if forged.msg ∉ signedSet_w ∧ idx_w(forged) = some j then
              Pr[= forged.dom | trapdoorSample (cache_w forged)] else 0`

is a lower bound for the winner-slot-restricted per-target embedding win
(`reservoir_embed_winnerIdx_le`'s left side, i.e. the right side of the floor-free coupling).  The
front target average `∑' y, Pr[= y] · embedTrapIdxImpl … j y` is lifted to the signed-set-augmented
index run (`map_run_embedTrapIdxSigImpl_proj`, signed set passive) and then to the inline-fresh run
(`evalDist_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl`).  On the inline-fresh run the
freshness recovery (`embedTrapIdxSigImpl_fresh_idx_cache_eq`) makes the diagonal
`cache(forged) = some y` automatic on the freshness-confined winner slot, so the front `y` is
recovered as the cached image and the embed win event's literal `cache(forged) = some y` is matched;
the residual freshness restriction `forged.msg ∉ signedSet` only *decreases* the inline-fresh-run
expectation relative to the (freshness-free) embed win mass, so the bound is an inequality. -/
lemma freshSig_winnerSlot_deferred_le_embed [DecidableEq Domain] [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    (∑' w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
        Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (adv.main pk)).run
            ((((∅, 0), fun _ => none), ∅))] *
          (if w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j then
              Pr[= w.1.2.2 | psf.trapdoorSample pk sk
                ((w.2.1.1.1 (w.1.2.1, w.1.1)).getD default)]
            else 0)) ≤
      ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
          Pr[= true | (do
            let r ← (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
              (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))
            let x ← psf.trapdoorSample pk sk ((r.2.1.1 (r.1.2.1, r.1.1)).getD y)
            pure (decide (r.1.2.2 = x) && decide (r.2.1.1 (r.1.2.1, r.1.1) = some y) &&
              decide (r.2.2 (r.1.2.1, r.1.1) = some j)) : ProbComp Bool)] := by
  classical
  -- Rewrite each per-target embed win on the Sig-augmented run (signed set passive), then express
  -- the win mass as a `tsum` over the run output `r`.
  rw [tsum_probOutput_embedTrapFreshIdxSig_mul_eq_frontDraw psf M Salt pk sk j (adv.main pk)
    ((((∅, 0), fun _ => none), ∅))]
  refine ENNReal.tsum_le_tsum fun y => ?_
  refine mul_le_mul' le_rfl ?_
  -- Lift the un-augmented embed run on the RHS to the signed-set-augmented run.
  rw [show (simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) (adv.main pk)).run
        (((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ)), (fun _ => none))
      = Prod.map id (Prod.fst :
          (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M →
            ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) <$>
        (simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((((∅, 0), fun _ => none), ∅)) from
    (map_run_embedTrapIdxSigImpl_proj psf M Salt pk sk j y (adv.main pk)
      ((((∅, 0), fun _ => none), ∅))).symm]
  rw [bind_map_left]
  -- Express the win mass as a `tsum` over the Sig run output and compare termwise.
  rw [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun w => ?_
  simp only [Prod.map, id_eq]
  -- Compare `Pr[= w | run] · Wf w ≤ Pr[= w | run] · winContinuation w`; off-support both vanish,
  -- on-support the freshness recovery aligns the literals.
  by_cases hsupp : w ∈ support ((simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y)
      (adv.main pk)).run ((((∅, 0), fun _ => none), ∅)))
  · refine mul_le_mul' le_rfl ?_
    -- The win predicate is `decide (r.dom = x) && decide (cache forged = some y) &&
    -- decide (idx forged = some j)`, with the trapdoor draw `x ← trapdoor ((cache forged).getD y)`.
    by_cases hWf : w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j
    · obtain ⟨hfresh, hidx⟩ := hWf
      -- Freshness recovery on the Sig run: `idx forged = some j` and forged unsigned force
      -- `cache forged = some y`.
      have hcache : w.2.1.1.1 (w.1.2.1, w.1.1) = some y :=
        embedTrapIdxSigImpl_fresh_idx_cache_eq psf M Salt pk sk j y (adv.main pk) w hsupp
          (w.1.2.1, w.1.1) hidx hfresh
      rw [if_pos ⟨hfresh, hidx⟩, probOutput_bind_eq_tsum]
      -- The continuation `pure (decide (dom = x) && decide (cache = some y) && decide (idx = j))`
      -- has both run-only literals `true`; it reduces to matching `dom = x`, so the `tsum` over `x`
      -- collapses to the single diagonal term at `x = dom`.
      refine le_of_eq ?_
      simp only [hcache, hidx, Option.getD_some, decide_true, Bool.and_true]
      rw [tsum_eq_single w.1.2.2 (fun x hx => by
        rw [probOutput_pure_eq_indicator]
        simp only [Set.indicator_apply, Set.mem_singleton_iff, eq_comm (a := true),
          decide_eq_true_eq, Ne.symm hx, if_false, mul_zero])]
      rw [probOutput_pure_eq_indicator]
      simp only [Set.indicator_apply, Set.mem_singleton_iff, eq_comm (a := true),
        decide_eq_true_eq, if_true, Function.const_apply, mul_one]
    · rw [if_neg hWf]; exact zero_le'
  · rw [probOutput_eq_zero_of_not_mem_support hsupp, zero_mul]; exact zero_le'

omit [DecidableEq Range] [Fintype Salt] in
/-- **The signed set only grows along the trap-count run.**  Every reachable final state's signed
set contains the start signed set: signing inserts the queried message and no step removes from the
signed set. -/
lemma progGameRunImplCombinedTrapCount_signedSet_grows (pk : PK) (sk : SK) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        s.1.1.1.2 ⊆ z.2.1.1.1.2 := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact subset_rfl
  | query_bind t mx ih =>
      intro s z hz
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        have := ih pv pst z hz; rw [hpst] at this; exact this
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            have := ih pv pst z hz; rw [hpst] at this; exact this
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            have := ih pv pst z hz; rw [hpst] at this; exact this
      · rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        have hih := ih pv pst z hz
        rw [hpst] at hih
        exact (Finset.subset_insert _ _).trans hih

omit [DecidableEq Range] [Fintype Salt] in
/-- **Write-once freezing of a programmed, unsigned key on the trap-count run.**  Once a key `k₀` is
cached (`cache_s(k₀) ≠ none`) and its message stays unsigned through the run (`k₀.2 ∉ z.signedSet`
at the reachable final state `z`), both its cached image and its recorded trapdoor preimage are
frozen: `cache_z(k₀) = cache_s(k₀)` and `table_z(k₀) = table_s(k₀)`.  Random-oracle misses fire only
on cache misses, so they cannot overwrite an already-cached `k₀`; the signing branch writes at
`(r, msg)` and inserts `msg` into the signed set, so if it touched `k₀` it would sign `k₀.2`,
contradicting the final-state freshness (the signed set only grows). -/
lemma progGameRunImplCombinedTrapCount_frozen (pk : PK) (sk : SK) (k₀ : Salt × M) :
    ∀ {β : Type}
      (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
      (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ)),
      s.1.1.1.1 k₀ ≠ none →
      ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
        k₀.2 ∉ z.2.1.1.1.2 →
        z.2.1.1.1.1 k₀ = s.1.1.1.1 k₀ ∧ z.2.1.2 k₀ = s.1.2 k₀ := by
  intro β oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro s hs z hz hfresh
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact ⟨rfl, rfl⟩
  | query_bind t mx ih =>
      intro s hs z hz hfresh
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind] at hz
      rcases (mem_support_bind_iff _ _ _).1 hz with ⟨⟨pv, pst⟩, hps, hz⟩
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨v, -, -, hpst⟩ := hps
        rw [hpst] at hz
        exact ih pv s hs z hz hfresh
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr] at hps
        cases hq : s.1.1.1.1 mc with
        | some v =>
            rw [hq] at hps
            simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hps
            obtain ⟨-, hpst⟩ := hps
            rw [hpst] at hz
            exact ih pv s hs z hz hfresh
        | none =>
            rw [hq] at hps
            simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
              Prod.mk.injEq] at hps
            obtain ⟨v, -, x, -, -, hpst⟩ := hps
            -- The miss is at `mc ≠ k₀` (since `cache_s(k₀) ≠ none = cache_s(mc)`), so `k₀` is
            -- untouched; apply the IH from the post-step state, which still has `cache(k₀) ≠ none`.
            have hne : k₀ ≠ mc := fun h => hs (by rw [h]; exact hq)
            obtain ⟨hcache, htbl⟩ := ih pv pst (by
              rw [hpst]; simp only [QueryCache.cacheQuery_of_ne _ _ hne]; exact hs) z hz hfresh
            rw [hcache, htbl, hpst]
            simp only [QueryCache.cacheQuery_of_ne _ _ hne, if_neg hne]
            exact ⟨trivial, trivial⟩
      · rw [progGameRunImplCombinedTrapCount_run_inr] at hps
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
          Prod.mk.injEq] at hps
        obtain ⟨r, -, v, -, x, -, -, hpst⟩ := hps
        -- The signing inserts `msg` into the signed set; since the post-state's signed set is
        -- contained in the final `z`'s signed set, and `k₀.2 ∉ z.signedSet`, we get `msg ≠ k₀.2`,
        -- hence `(r, msg) ≠ k₀`, so the signing step left `k₀` untouched.
        have hmsg : msg ≠ k₀.2 := by
          intro hmeq
          have hpst_sgn : k₀.2 ∈ pst.1.1.1.2 := by
            rw [hpst]; simp only [hmeq, Finset.mem_insert, true_or]
          have hgrow := progGameRunImplCombinedTrapCount_signedSet_grows psf M Salt pk sk
            (mx pv) pst z hz
          exact hfresh (hgrow hpst_sgn)
        have hk : k₀ ≠ (r, msg) := fun h => hmsg (by rw [h])
        obtain ⟨hcache, htbl⟩ := ih pv pst (by
          rw [hpst]; simp only [QueryCache.cacheQuery_of_ne _ _ hk]; exact hs) z hz hfresh
        rw [hcache, htbl, hpst]
        simp only [QueryCache.cacheQuery_of_ne _ _ hk, if_neg hk]
        exact ⟨trivial, trivial⟩

omit [DecidableEq Range] [Fintype Salt] in
/-- **Table-independence of any output/cache/idx/signedSet expectation on the trap-count run.**  The
trap handler never reads the write-only preimage table, so any output functional `F` of the output
and the projected `(cache, counter, idx, signedSet)` state has the same expectation from two start
states `s₁`, `s₂` that agree on everything except the table (`s₁.1.1 = s₂.1.1` and `s₁.2 = s₂.2`,
i.e. the cache/signed-set/bad components and the idx/counter components coincide).  Instance of the
generic state-relation transfer `tsum_probOutput_simulateQ_run_mul_of_rel`. -/
lemma progGameRunImplCombinedTrapCount_table_indep (pk : PK) (sk : SK)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (F : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (s₁ s₂ : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
        ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ))
    (h11 : s₁.1.1 = s₂.1.1) (h2 : s₁.2 = s₂.2) :
    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s₁] *
        F z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2))) =
      ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s₂] *
        F z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) := by
  classical
  exact OracleComp.DeferredSampling.tsum_probOutput_simulateQ_run_mul_of_rel
    (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa
    (fun u₁ u₂ => u₁.1.1 = u₂.1.1 ∧ u₁.2 = u₂.2)
    (fun t a b hab K hKinv => by
      obtain ⟨hb11, hb2⟩ := hab
      rcases t with (n | mc) | msg
      · rw [progGameRunImplCombinedTrapCount_run_inl_inl,
          progGameRunImplCombinedTrapCount_run_inl_inl]
        rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
          OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
        refine tsum_congr fun v => ?_
        rw [OracleComp.DeferredSampling.tsum_probOutput_pure_mul,
          OracleComp.DeferredSampling.tsum_probOutput_pure_mul]
        exact congrArg _ (hKinv v a b ⟨hb11, hb2⟩)
      · rw [progGameRunImplCombinedTrapCount_run_inl_inr,
          progGameRunImplCombinedTrapCount_run_inl_inr]
        have hcache : a.1.1.1.1 mc = b.1.1.1.1 mc := by rw [hb11]
        rw [hcache]
        cases hq : b.1.1.1.1 mc with
        | some v =>
            rw [OracleComp.DeferredSampling.tsum_probOutput_pure_mul,
              OracleComp.DeferredSampling.tsum_probOutput_pure_mul]
            exact hKinv v a b ⟨hb11, hb2⟩
        | none =>
            rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
              OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
              OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
            refine tsum_congr fun x => congrArg _ ?_
            rw [OracleComp.DeferredSampling.tsum_probOutput_pure_mul,
              OracleComp.DeferredSampling.tsum_probOutput_pure_mul]
            refine hKinv v _ _ ⟨?_, ?_⟩
            · simp only [hb11]
            · simp only [hb2]
      · rw [progGameRunImplCombinedTrapCount_run_inr, progGameRunImplCombinedTrapCount_run_inr]
        rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
          OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
        refine tsum_congr fun r => congrArg _ ?_
        rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
          OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
        refine tsum_congr fun v => congrArg _ ?_
        rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
          OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
        refine tsum_congr fun x => congrArg _ ?_
        rw [OracleComp.DeferredSampling.tsum_probOutput_pure_mul,
          OracleComp.DeferredSampling.tsum_probOutput_pure_mul]
        refine hKinv _ _ _ ⟨?_, ?_⟩
        · simp only [hb11]
        · simp only [hb2])
    (fun g st => F g ((((st.1.1.1.1, st.2.2), st.2.1), st.1.1.1.2)))
    (fun g u₁ u₂ huv => by
      obtain ⟨hu11, hu2⟩ := huv
      have hst : ((((u₁.1.1.1.1, u₁.2.2), u₁.2.1), u₁.1.1.1.2) :
            (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
          = ((((u₂.1.1.1.1, u₂.2.2), u₂.2.1), u₂.1.1.1.2)) := by
        rw [show u₁.1.1.1.1 = u₂.1.1.1.1 from by rw [hu11],
          show u₁.1.1.1.2 = u₂.1.1.1.2 from by rw [hu11],
          show u₁.2.1 = u₂.2.1 from by rw [hu2], show u₁.2.2 = u₂.2.2 from by rw [hu2]]
      simp only []
      rw [hst])
    s₁ s₂ ⟨h11, h2⟩

open Classical in
omit [DecidableEq Range] [Fintype Salt] in
/-- **Frozen-table expectation on the trap-count run.**  When the forged key `k₀` is already cached
at the start (`cache_s(k₀) ≠ none`) and the output functional `G` vanishes off the freshness event
`k₀.2 ∉ signedSet`, the recorded table at `k₀` is frozen on the relevant support, so the
`G · 1_{table(k₀) = some sStar}` expectation factors as the constant frozen indicator
`1_{table_s(k₀) = some sStar}` times the `G` expectation. -/
lemma progGameRunImplCombinedTrapCount_table_frozen_eq (pk : PK) (sk : SK)
    (k₀ : Salt × M) (sStar : Domain)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (G : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (hGfresh : ∀ b w, k₀.2 ∈ w.2 → G b w = 0)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ))
    (hs : s.1.1.1.1 k₀ ≠ none) :
    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
        (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
          (if z.2.1.2 k₀ = some sStar then 1 else 0))) =
      (if s.1.2 k₀ = some sStar then 1 else 0) *
        ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
          G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2) ) := by
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun z => ?_
  by_cases hz : z ∈ support
      ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s)
  · by_cases hzfresh : k₀.2 ∈ z.2.1.1.1.2
    · rw [hGfresh z.1 _ (by exact hzfresh)]; ring
    · obtain ⟨-, htbl⟩ := progGameRunImplCombinedTrapCount_frozen psf M Salt pk sk k₀ oa s hs z hz
        hzfresh
      rw [htbl]; ring
  · rw [probOutput_eq_zero_of_not_mem_support hz]; ring

open Classical in
omit [DecidableEq Range] [Fintype Salt] in
/-- **Per-step deferral of one write-only trapdoor draw on the trap-count run (state-general
form).**  For a fixed key `k₀` and recorded value `sStar`, and any nonnegative output functional
`G` of the run output and the projected `(cache, counter, idx, signedSet)` state, the trap-count run
expectation of `G · 1_{table(k₀) = some sStar}` equals the run expectation of `G · D s`, where the
*deferred* value `D s z` is:

* the frozen indicator `1_{table_s(k₀) = some sStar}` if `k₀` was already programmed at the start
  state `s` (`cache_s(k₀) ≠ none`); or
* the deferred trapdoor-draw probability `Pr[= sStar | trapdoorSample (cache_z(k₀))]` if `k₀` is
  freshly programmed during the run (`cache_s(k₀) = none` and `cache_z(k₀) ≠ none`), and `0` if `k₀`
  is never programmed (`cache_z(k₀) = none`).

The recorded preimage `x ← trapdoorSample (cache k₀)` is sampled write-only at the `k₀` programming
event and never read, so its position in the adaptive fold is irrelevant: at the programming step
the inline `x`-draw is integrated against the frozen continuation (`cache(k₀)` and `table(k₀)` are
both frozen afterwards), turning `1_{table(k₀) = some sStar}` into the trapdoor-draw probability;
off the programming step the table at `k₀` is untouched, so the IH carries through.  This is the
defer-to-end twin of the front-loading lift, *keeping* the forged draw rather than dropping it. -/
lemma progGameRunImplCombinedTrapCount_table_defer (pk : PK) (sk : SK)
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (k₀ : Salt × M) (sStar : Domain)
    {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (G : β →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞)
    (hGfresh : ∀ b w, k₀.2 ∈ w.2 → G b w = 0) :
    ∀ (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
        (((Salt × M) → Option ℕ) × ℕ)),
      (s.1.2 k₀ ≠ none → s.1.1.1.1 k₀ ≠ none) →
      (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
          (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
            (if z.2.1.2 k₀ = some sStar then 1 else 0))) =
        ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s] *
          (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
            (match s.1.1.1.1 k₀ with
              | some _ => (if s.1.2 k₀ = some sStar then 1 else 0)
              | none =>
                  match z.2.1.1.1.1 k₀ with
                  | some v => Pr[= sStar | psf.trapdoorSample pk sk v]
                  | none => 0)) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s htc
      simp only [simulateQ_pure, StateT.run_pure,
        OracleComp.DeferredSampling.tsum_probOutput_pure_mul]
      -- At `pure`, the final state is the start state, so the table at `k₀` is `s.1.2 k₀`.
      rcases hc : s.1.1.1.1 k₀ with _ | v
      · -- `k₀` unprogrammed at start (and at end): the deferred branch gives `0`; the table/cache
        -- lockstep `htc` forces `table_s(k₀) = none`, so the indicator branch is also `0`.
        have htbl : s.1.2 k₀ = none := by
          by_contra hne; exact (htc hne) hc
        rw [if_neg (by rw [htbl]; simp)]
      · rfl
  | query_bind t mx ih =>
      intro s htc
      -- **Branch A: `k₀` already programmed at the start.**  The deferred value is the constant
      -- frozen indicator; both sides factor through the frozen-table expectation lemma.
      rcases hcs : s.1.1.1.1 k₀ with _ | v₀
      · -- **Branch B: `k₀` not yet programmed at the start.**  Split the leading step from the
        -- continuation and integrate the (single) `k₀`-programming draw to the front.
        simp only [hcs]
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind]
        rcases t with (n | mc) | msg
        · -- Uniform query: the state is untouched, `cache(k₀)` stays `none`; apply the IH at `s`.
          rw [progGameRunImplCombinedTrapCount_run_inl_inl, bind_assoc]
          simp only [pure_bind]
          rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
            OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
          refine tsum_congr fun v => congrArg _ ?_
          have hih := ih v s htc
          simp only [hcs] at hih
          exact hih
        · -- Random-oracle query at `mc`.
          rw [progGameRunImplCombinedTrapCount_run_inl_inr]
          cases hmcq : s.1.1.1.1 mc with
          | some v =>
              -- Cache hit: state untouched; apply the IH at `s`.
              simp only [hmcq, pure_bind]
              have hih := ih v s htc
              simp only [hcs] at hih
              exact hih
          | none =>
              have htbls : s.1.2 k₀ = none := by
                by_contra hne; exact (htc hne) hcs
              simp only [hmcq, bind_assoc, pure_bind]
              by_cases hmck : mc = k₀
              · -- **The forged random-oracle miss: integrate the single trapdoor draw.**
                subst hmck
                rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
                  OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
                refine tsum_congr fun v => congrArg _ ?_
                -- Abbreviate the per-`(v, x)` `G`-expectation `Q x` from the post-state.
                set Q : Domain → ℝ≥0∞ := fun x =>
                  ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
                      (mx v)).run
                      ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                        fun t' => if t' = mc then some x else s.1.2 t'),
                        (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1)] *
                    G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) with hQ
                -- **LHS inner**, per `x`: apply the deferral IH at the post-state (where `cache mc`
                -- is `some v ≠ none`), turning `1_{table_z(mc) = sStar}` into the *frozen* value
                -- `1_{table_post(mc) = sStar} = 1_{x = sStar}`; then the constant factors out.
                have hLHS : ∀ x : Domain,
                    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
                        (mx v)).run
                        ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1)] *
                      (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
                        (if z.2.1.2 mc = some sStar then 1 else 0)))
                      = (if x = sStar then 1 else 0) * Q x := by
                  intro x
                  have hihx := ih v
                    ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                        fun t' => if t' = mc then some x else s.1.2 t'),
                        (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1) (by
                      simp only [QueryCache.cacheQuery_self]; exact fun _ => Option.some_ne_none v)
                  simp only [QueryCache.cacheQuery_self] at hihx
                  rw [hihx]
                  -- the post-state's `table mc = some x`, so the frozen indicator is `1_{x=sStar}`
                  simp only [if_true, Option.some.injEq]
                  rw [hQ]
                  simp only []
                  rw [← ENNReal.tsum_mul_left]
                  refine tsum_congr fun z => ?_; ring
                -- **RHS inner**, per `x`: the cache at `mc` is frozen to `some v`, so the deferred
                -- value is the constant `Pr[= sStar | trapdoorSample v]`; factor it out.
                have hRHS : ∀ x : Domain,
                    (∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
                        (mx v)).run
                        ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1)] *
                      (G z.1 ((((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2)) *
                        (match z.2.1.1.1.1 mc with
                          | some w => Pr[= sStar | psf.trapdoorSample pk sk w]
                          | none => 0)))
                      = Pr[= sStar | psf.trapdoorSample pk sk v] * Q x := by
                  intro x
                  rw [hQ]
                  simp only []
                  rw [← ENNReal.tsum_mul_left]
                  refine tsum_congr fun z => ?_
                  by_cases hz : z ∈ support
                      ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (mx v)).run
                        ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1))
                  · by_cases hzfresh : mc.2 ∈ z.2.1.1.1.2
                    · -- `mc.2` signed at `z` ⟹ `G = 0`, so the term vanishes on both sides.
                      rw [hGfresh z.1 _ (by exact hzfresh)]; ring
                    · have hpostc : ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                          fun t' => if t' = mc then some x else s.1.2 t'),
                          (fun t' => if t' = mc then some s.2.2 else s.2.1 t'),
                          s.2.2 + 1).1.1.1.1 mc ≠ none := by
                        simp only [QueryCache.cacheQuery_self]; exact Option.some_ne_none v
                      obtain ⟨hzcache, -⟩ := progGameRunImplCombinedTrapCount_frozen psf M Salt pk
                        sk mc (mx v) _ hpostc z hz hzfresh
                      rw [hzcache]
                      simp only [QueryCache.cacheQuery_self]; ring
                  · rw [probOutput_eq_zero_of_not_mem_support hz]; ring
                -- **Combine.**  Per `x`, the inner sum is `Pr[= sStar | trapdoorSample v] · Q x` on
                -- the right and `1_{x = sStar} · Q x` on the left, and `Q` is table-independent
                -- (`progGameRunImplCombinedTrapCount_table_indep`), so `Q x = Q sStar`; integrating
                -- `x ← trapdoorSample v` turns the left indicator into `Pr[= sStar | trapdoor v]`.
                rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
                  OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
                simp only [hLHS, hRHS]
                -- `Q` is independent of the table value `x`, so `Q x = Q sStar` for all `x`.
                have hQindep : ∀ x : Domain, Q x = Q sStar := fun x => by
                  rw [hQ]
                  exact progGameRunImplCombinedTrapCount_table_indep psf M Salt pk sk (mx v) _ _ _
                    rfl rfl
                simp_rw [hQindep]
                -- LHS: `∑' x, Pr[= x] · (1_{x = sStar} · Q sStar) = Pr[= sStar | trapdoor v] · Q`.
                rw [show (∑' x : Domain, Pr[= x | psf.trapdoorSample pk sk v] *
                        ((if x = sStar then 1 else 0) * Q sStar))
                      = Pr[= sStar | psf.trapdoorSample pk sk v] * Q sStar from by
                    rw [tsum_eq_single sStar (fun x hx => by rw [if_neg hx, zero_mul, mul_zero])]
                    rw [if_pos rfl, one_mul]]
                -- RHS: `∑' x, Pr[= x] · (Pr[= sStar | trapdoor v] · Q sStar) = 1 · (… · Q)`.
                rw [ENNReal.tsum_mul_right,
                  tsum_probOutput_eq_one' (hNF v).probFailure_eq_zero, one_mul]
              · -- Miss at `mc ≠ k₀`: `cache(k₀)` stays `none`; apply the IH at the post-state.
                rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
                  OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
                refine tsum_congr fun v => congrArg _ ?_
                rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
                  OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
                refine tsum_congr fun x => congrArg _ ?_
                -- Apply the IH at the post-state; `cache(k₀)` is unchanged (miss at `mc ≠ k₀`),
                -- so its outer deferred branch stays `none`, matching the goal.
                have hih := ih v
                  ((((s.1.1.1.1.cacheQuery mc v, s.1.1.1.2), s.1.1.2),
                      fun t' => if t' = mc then some x else s.1.2 t'),
                      (fun t' => if t' = mc then some s.2.2 else s.2.1 t'), s.2.2 + 1) (by
                    simp only [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hmck), hcs, if_neg
                      (Ne.symm hmck), htbls]
                    exact fun h => absurd rfl h)
                simp only [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hmck), hcs] at hih
                exact hih
        · -- Signing query on `msg`.
          rw [progGameRunImplCombinedTrapCount_run_inr]
          simp only [bind_assoc, pure_bind]
          have htbls : s.1.2 k₀ = none := by
            by_contra hne; exact (htc hne) hcs
          by_cases hmsg : msg = k₀.2
          · -- Signing the forged message inserts `k₀.2` into the (monotone) signed set, so every
            -- continuation has `k₀.2 ∈ signedSet` and `G = 0`; both sides vanish termwise.
            rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
              OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
            refine tsum_congr fun r => congrArg _ ?_
            rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
              OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
              OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
            refine tsum_congr fun x => congrArg _ ?_
            refine tsum_congr fun z => ?_
            by_cases hz : z ∈ support
                ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (mx (r, x))).run
                  ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
                    s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
                    fun t' => if t' = (r, msg) then some x else s.1.2 t'),
                    (fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1))
            · have hgrow := progGameRunImplCombinedTrapCount_signedSet_grows psf M Salt pk sk
                (mx (r, x)) _ z hz
              have hmem : k₀.2 ∈ z.2.1.1.1.2 :=
                hgrow (by simp only [hmsg, Finset.mem_insert, true_or])
              rw [hGfresh z.1 _ hmem]; ring
            · rw [probOutput_eq_zero_of_not_mem_support hz]; ring
          · -- `msg ≠ k₀.2` forces `(r, msg) ≠ k₀`, so `cache(k₀)` stays `none`; apply the IH.
            rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
              OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
            refine tsum_congr fun r => congrArg _ ?_
            rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
              OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
            refine tsum_congr fun v => congrArg _ ?_
            rw [OracleComp.DeferredSampling.tsum_probOutput_bind_mul,
              OracleComp.DeferredSampling.tsum_probOutput_bind_mul]
            refine tsum_congr fun x => congrArg _ ?_
            have hk : k₀ ≠ (r, msg) := fun h => hmsg (by rw [h])
            have hih := ih (r, x)
              ((((s.1.1.1.1.cacheQuery (r, msg) v, insert msg s.1.1.1.2),
                  s.1.1.2 || saltKeyed M Salt s.1.1.1.1 r),
                  fun t' => if t' = (r, msg) then some x else s.1.2 t'),
                  (fun t' => if t' = (r, msg) then some s.2.2 else s.2.1 t'), s.2.2 + 1) (by
                simp only [QueryCache.cacheQuery_of_ne _ _ hk, hcs, if_neg hk, htbls]
                exact fun h => absurd rfl h)
            simp only [QueryCache.cacheQuery_of_ne _ _ hk, hcs] at hih
            exact hih
      · simp only [hcs]
        rw [progGameRunImplCombinedTrapCount_table_frozen_eq psf M Salt pk sk k₀ sStar _ G hGfresh s
          (by rw [hcs]; exact Option.some_ne_none v₀), ← ENNReal.tsum_mul_left]
        refine tsum_congr fun z => ?_; ring

open Classical in
omit [Fintype Salt] in
/-- **Step-2 trap-side table-defer to the common freshness-confined deferred functional.**  The
freshness-confined index-tagged trap-exact-match mass — the trap event
`forged.msg ∉ signedSet ∧ table(forged) = some forged.dom ∧ idx(forged) = some j` on the
counter-augmented trapdoor-recording run `progGameRunImplCombinedTrapCount` — is bounded by the
inline-fresh-run expectation of the freshness-confined winner-slot deferred-trapdoor functional

  `Wf w := if forged.msg ∉ signedSet_w ∧ idx_w(forged) = some j then
              Pr[= forged.dom | trapdoorSample (cache_w forged)] else 0`.

This is the genuinely-new (answer-irrelevant) content of GPV Step-2: at the freshness-confined
forged key the write-only trapdoor preimage `x ← trapdoorSample (cache forged)` recorded inline into
the
table is *never read* (an unsigned forged key is a random-oracle miss whose preimage enters only the
write-only table, never the adversary view), so it commutes to the end of the adaptive fold and
becomes a post-run independent trapdoor draw against the cached image.  Freshness is exactly what
makes this draw deferrable; a *signed* key returns `(r, x)` to the adversary, so its table draw is
not deferrable, which is why dropping freshness falsifies the bound. -/
lemma trap_freshSig_le_winnerSlot_deferred [Inhabited Range]
    (pk : PK) (sk : SK) (j : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c)) :
    Pr[fun w : (M × (Salt × Domain)) ×
          (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
            (((Salt × M) → Option ℕ) × ℕ)) =>
          (w.1.1 ∉ w.2.1.1.1.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
            w.2.2.1 (w.1.2.1, w.1.1) = some j |
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)]
      ≤ ∑' w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M),
        Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) (adv.main pk)).run
            ((((∅, 0), fun _ => none), ∅))] *
          (if w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j then
              Pr[= w.1.2.2 | psf.trapdoorSample pk sk
                ((w.2.1.1.1 (w.1.2.1, w.1.1)).getD default)]
            else 0) := by
  classical
  -- Abbreviate the trap-state → fresh-sig-state projection (drop the freshness Bool flag and the
  -- write-only trapdoor table; reshape to the fresh-sig `(((cache × counter) × idx) × signedSet)`).
  set projS : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
        × (((Salt × M) → Option ℕ) × ℕ) →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M :=
    fun s => ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2)) with hprojS
  -- **Transport the RHS fresh-sig-run expectation onto the trap-count run.**  By the
  -- distribution-level projection, the fresh-sig run is the trap-count run mapped by
  -- `projS`, so the
  -- RHS expectation of `Wf` over the fresh-sig run equals its expectation over the trap-count run
  -- precomposed with `Prod.map id projS`.
  have hRHS : (∑' w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk)
          (adv.main pk)).run ((((∅, 0), fun _ => none), ∅))] *
        (if w.1.1 ∉ w.2.2 ∧ w.2.1.2 (w.1.2.1, w.1.1) = some j then
            Pr[= w.1.2.2 | psf.trapdoorSample pk sk
              ((w.2.1.1.1 (w.1.2.1, w.1.1)).getD default)]
          else 0)) =
      ∑' z, Pr[= z | (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)] *
        (if z.1.1 ∉ (projS z.2).2 ∧ (projS z.2).1.2 (z.1.2.1, z.1.1) = some j then
            Pr[= z.1.2.2 | psf.trapdoorSample pk sk
              (((projS z.2).1.1.1 (z.1.2.1, z.1.1)).getD default)]
          else 0) := by
    have hmap := map_run_progGameRunImplCombinedTrapCount_freshSig_proj psf M Salt pk sk hNF
      (adv.main pk)
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
        (fun _ => none), 0)
    simp only [hprojS] at hmap ⊢
    -- Pointwise: the fresh-sig output probability is the trap-count run mapped by `projS`.
    have hpt : ∀ w, Pr[= w | (simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk)
          (adv.main pk)).run ((((∅, 0), fun _ => none), ∅))]
        = Pr[= w | Prod.map id
            (fun s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ×
                ((Salt × M) → Option Domain)) × (((Salt × M) → Option ℕ) × ℕ) =>
              ((((s.1.1.1.1, s.2.2), s.2.1), s.1.1.1.2) :
                (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)) <$>
            (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (adv.main pk)).run
              (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
                (fun _ => none), 0)] :=
      fun w => by rw [probOutput, probOutput, hmap]
    simp_rw [hpt]
    rw [OracleComp.DeferredSampling.tsum_probOutput_map_mul]
    refine tsum_congr fun z => ?_
    simp only [Prod.map, id_eq]
  rw [hRHS]
  -- **The per-run table-defer (the answer-irrelevant content).**  Both sides are
  -- now expectations over the *same* trap-count run; the LHS reads the recorded table at the forged
  -- point (`1_{table(forged) = some forged.dom}`), the RHS the deferred trapdoor draw against the
  -- cached image (`Pr[= forged.dom | trapdoorSample (cache forged)]`).  On the freshness-confined
  -- winner slot the recorded entry is the inline write-only draw `x ← trapdoorSample (cache
  -- forged)` sampled at the forged random-oracle miss and never read; its *expected* indicator over
  -- the run equals the deferred draw probability.
  --
  -- ⚠ This is NOT a per-final-state inequality (it FAILS pointwise: at a state whose table is
  -- already frozen to `some d₀`, the LHS indicator is `1_{d₀ = forged.dom}` while the RHS is
  -- `Pr[= forged.dom | trapdoorSample (cache forged)] < 1`).  It holds only in *expectation*: the
  -- recorded `x` is itself random (drawn at the forged miss), independent of `(output, cache)`
  -- given the run, so `E[1_{table(forged) = forged.dom}] = Pr[= forged.dom | trapdoorSample (cache
  -- forged)]`.  Mechanizing it requires *deferring* the single answer-irrelevant write-only draw
  -- `x` from its inline position at the forged miss to the end of the adaptive `simulateQ` fold (it
  -- commutes past every subsequent step because the continuation never reads `table(forged)` or the
  -- frozen `cache(forged)`), matching it to a post-run draw of `trapdoorSample (cache forged)`.
  -- The projection `map_run_progGameRunImplCombinedTrapCount_freshSig_proj` *drops* every table
  -- draw via `evalDist_bind_const_neverFails`; the defer-to-end induction over the trap run that
  -- keeps the deferred draw is `progGameRunImplCombinedTrapCount_table_defer`.  Below the FRESH
  -- conjunct `w.1.1 ∉ w.2.1.1.1.2` is carried throughout.
  rw [probEvent_eq_tsum_ite]
  refine le_of_eq ?_
  classical
  -- Decompose the output-dependent forged-key indicator over a fixed key/value pair `p`, swap the
  -- order of summation, and apply the (fixed-key) table-defer per `p`.  Recombining over `p` gives
  -- the deferred functional with the cache-read trapdoor probability.
  set proj2 : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain))
        × (((Salt × M) → Option ℕ) × ℕ) →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M :=
    fun st => ((((st.1.1.1.1, st.2.2), st.2.1), st.1.1.1.2)) with hproj2
  -- The per-pair selector functional.
  set Gp : (Salt × M) × Domain → (M × (Salt × Domain)) →
      (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M → ℝ≥0∞ :=
    fun p b w => if (b.2.1, b.1) = p.1 ∧ b.2.2 = p.2 ∧ b.1 ∉ w.2 ∧ w.1.2 p.1 = some j
      then 1 else 0 with hGp
  set run := (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (adv.main pk)).run
    ((((∅, ∅), false), fun _ => none), (fun _ => none), 0) with hrun
  -- **LHS = double sum.**  The forged-key indicator collapses to the single pair
  -- `p = (forged, forged.dom)`.
  have hLHSdecomp : (∑' z, if (z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.1.2 (z.1.2.1, z.1.1) = some z.1.2.2) ∧
          z.2.2.1 (z.1.2.1, z.1.1) = some j then Pr[= z | run] else 0)
      = ∑' p : (Salt × M) × Domain, ∑' z,
          Pr[= z | run] * (Gp p z.1 (proj2 z.2) * (if z.2.1.2 p.1 = some p.2 then 1 else 0)) := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun z => ?_
    simp only [hGp, hproj2]
    rw [tsum_eq_single ((z.1.2.1, z.1.1), z.1.2.2) (fun p hp => by
      rw [show (if (z.1.2.1, z.1.1) = p.1 ∧ z.1.2.2 = p.2 ∧ z.1.1 ∉ z.2.1.1.1.2 ∧
            z.2.2.1 p.1 = some j then (1 : ℝ≥0∞) else 0) = 0 from by
        refine if_neg ?_
        rintro ⟨h1, h2, -, -⟩; exact hp (by rw [Prod.ext_iff]; exact ⟨h1.symm, h2.symm⟩),
        zero_mul, mul_zero])]
    simp only [true_and]
    by_cases hev : (z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.1.2 (z.1.2.1, z.1.1) = some z.1.2.2) ∧
        z.2.2.1 (z.1.2.1, z.1.1) = some j
    · obtain ⟨⟨hfresh, htbl⟩, hidx⟩ := hev
      rw [if_pos ⟨⟨hfresh, htbl⟩, hidx⟩, if_pos ⟨hfresh, hidx⟩, if_pos htbl]; ring
    · rw [if_neg hev]
      by_cases htbl : z.2.1.2 (z.1.2.1, z.1.1) = some z.1.2.2
      · have hcond : ¬(z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.2.1 (z.1.2.1, z.1.1) = some j) := by
          rintro ⟨hfresh, hidx⟩; exact hev ⟨⟨hfresh, htbl⟩, hidx⟩
        rw [if_pos htbl, mul_one, if_neg hcond, mul_zero]
      · rw [if_neg htbl, mul_zero, mul_zero]
  -- **Per-pair table-defer.**  Apply the fixed-key table-defer lemma at `(k₀, sStar) = p` with the
  -- selector `Gp p` (which vanishes off the freshness event, as required).
  have hbridge : ∀ p : (Salt × M) × Domain,
      (∑' z, Pr[= z | run] * (Gp p z.1 (proj2 z.2) * (if z.2.1.2 p.1 = some p.2 then 1 else 0)))
        = ∑' z, Pr[= z | run] * (Gp p z.1 (proj2 z.2) *
            (match (proj2 z.2).1.1.1 p.1 with
              | some w => Pr[= p.2 | psf.trapdoorSample pk sk w]
              | none => 0)) := by
    intro p
    have hGfreshp : ∀ b w, p.1.2 ∈ w.2 → Gp p b w = 0 := by
      intro b w hmem
      rw [hGp]; refine if_neg ?_
      rintro ⟨hbp, -, hbw, -⟩
      exact hbw (by rw [show b.1 = p.1.2 from by rw [← hbp]]; exact hmem)
    have hdefer := progGameRunImplCombinedTrapCount_table_defer psf M Salt pk sk hNF p.1 p.2
      (adv.main pk) (Gp p) hGfreshp
      (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
        (fun _ => none), 0) (by simp)
    -- the empty start has `cache p.1 = none`, so the deferred outer match reduces to the inner
    -- `match cache_z p.1`.
    simp only [hrun, hproj2] at hdefer ⊢
    refine hdefer.trans (tsum_congr fun z => congrArg _ (congrArg _ ?_))
    rcases (((z.2.1.1.1.1, z.2.2.2), z.2.2.1), z.2.1.1.1.2).1.1.1 p.1 with _ | w <;> rfl
  -- **RHS = double sum.**  The deferred functional likewise collapses to the single forged pair.
  have hRHSdecomp : (∑' z, Pr[= z | run] *
          (if z.1.1 ∉ (proj2 z.2).2 ∧ (proj2 z.2).1.2 (z.1.2.1, z.1.1) = some j then
            Pr[= z.1.2.2 | psf.trapdoorSample pk sk
              (((proj2 z.2).1.1.1 (z.1.2.1, z.1.1)).getD default)]
          else 0))
      = ∑' p : (Salt × M) × Domain, ∑' z,
          Pr[= z | run] * (Gp p z.1 (proj2 z.2) *
            (match (proj2 z.2).1.1.1 p.1 with
              | some w => Pr[= p.2 | psf.trapdoorSample pk sk w]
              | none => 0)) := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun z => ?_
    simp only [hGp, hproj2]
    rw [tsum_eq_single ((z.1.2.1, z.1.1), z.1.2.2) (fun p hp => by
      rw [show (if (z.1.2.1, z.1.1) = p.1 ∧ z.1.2.2 = p.2 ∧ z.1.1 ∉ z.2.1.1.1.2 ∧
            z.2.2.1 p.1 = some j then (1 : ℝ≥0∞) else 0) = 0 from by
        refine if_neg ?_
        rintro ⟨h1, h2, -, -⟩; exact hp (by rw [Prod.ext_iff]; exact ⟨h1.symm, h2.symm⟩),
        zero_mul, mul_zero])]
    simp only [true_and]
    -- diagonal `p = (forged, dom)`: `Gp = 1_{fresh ∧ idx=j}` and the deferred value reads
    -- `cache_z(forged)`; on the run support `idx = some j` forces `cache ≠ none` (idx/table/cache
    -- lockstep), so it matches the `getD default` form.
    by_cases hz : z ∈ support run
    · by_cases hfi : z.1.1 ∉ z.2.1.1.1.2 ∧ z.2.2.1 (z.1.2.1, z.1.1) = some j
      · obtain ⟨hfresh, hidx⟩ := hfi
        rw [if_pos ⟨hfresh, hidx⟩, if_pos ⟨hfresh, hidx⟩]
        -- recover `cache ≠ none` from `idx = some j` via the lockstep invariants
        have hzrun : z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
            (adv.main pk)).run ((((∅, ∅), false), fun _ => none), (fun _ => none), 0)) := by
          rw [← hrun]; exact hz
        have hidxne : z.2.2.1 (z.1.2.1, z.1.1) ≠ none := by rw [hidx]; exact Option.some_ne_none j
        have htblne : z.2.1.2 (z.1.2.1, z.1.1) ≠ none :=
          (progGameRunImplCombinedTrapCount_idx_iff_table psf M Salt pk sk (adv.main pk)
            ((((∅, ∅), false), fun _ => none), (fun _ => none), 0)
            (fun k => by simp) z hzrun (z.1.2.1, z.1.1)).2 hidxne
        obtain ⟨xv, htbleq⟩ := Option.ne_none_iff_exists'.1 htblne
        obtain ⟨w, hcache, -⟩ := progGameRunImplCombinedTrapCount_table_support psf M Salt pk sk
          (adv.main pk) ((((∅, ∅), false), fun _ => none), (fun _ => none), 0)
          (fun k x hx => by simp at hx) z hzrun (z.1.2.1, z.1.1) xv htbleq
        rw [hcache, Option.getD_some]; ring
      · simp only [if_neg hfi, zero_mul, mul_zero]
    · rw [probOutput_eq_zero_of_not_mem_support hz]; ring
  -- **Combine.**  `LHS = (hLHSdecomp) ∑∑ indicator = (hbridge) ∑∑ deferred = (hRHSdecomp) RHS`.
  rw [hLHSdecomp]
  rw [show (∑' p : (Salt × M) × Domain, ∑' z, Pr[= z | run] *
        (Gp p z.1 (proj2 z.2) * (if z.2.1.2 p.1 = some p.2 then 1 else 0)))
      = ∑' p : (Salt × M) × Domain, ∑' z, Pr[= z | run] *
        (Gp p z.1 (proj2 z.2) *
          (match (proj2 z.2).1.1.1 p.1 with
            | some w => Pr[= p.2 | psf.trapdoorSample pk sk w]
            | none => 0)) from tsum_congr fun p => hbridge p]
  rw [← hRHSdecomp]

open Classical in
omit [Fintype Salt] in
/-- **The per-slot front-loading deferred-sampling coupling (floor-free form).**

The *index-tagged* trap-exact-match mass at slot `j` — the trap event on the counter-augmented run
`progGameRunImplCombinedTrapCount` restricted to the event that the forged point was *programmed at
counter value `j`* — is bounded by the **floor-free** per-target embedding win
`S (some j) = ∑' y, Pr[= y | $ᵗ Range] · Pr[win | embedTrapImpl … j y]`, with **no** budget /
reservoir factor.  This is the genuine deferred-sampling content of GPV Step-2: at the fixed slot
`j` the trap run's inline uniform winner draw `v⋆ ← $ᵗ Range` (drawn *inside* the `simulateQ` fold
at the adaptively-determined `j`-th programming step) must be pushed to the front and re-expressed
as the embedded target `y ← $ᵗ Range` (drawn *outside* the fold), mirroring
`evalDist_gpvRealImpl_eq_drawList_gpvRealImplTape`; the embedded slot is then `j` and the win event
couples to the trap run's write-only `table(forged) = trapdoorSample (cache(forged))`.

The budget-scaled form `reservoir_embed_commute_winner` follows from this by the reservoir floor
arithmetic (`probOutput_reservoirWinnerIndex_eq` at `j < qSign + qHash`, the recorded-index budget
`progGameRunImplCombinedTrapCount_idx_lt_budget` clearing the `j ≥ qSign + qHash` tail). -/
lemma reservoir_embed_commute_winner_floorFree [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) (j : ℕ) :
    Pr[fun w : (M × (Salt × Domain)) ×
          (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
            (((Salt × M) → Option ℕ) × ℕ)) =>
          ((decide (w.1.1 ∉ w.2.1.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
            w.2.2.1 (w.1.2.1, w.1.1) = some j |
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)]
      ≤ ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x) &&
                decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  -- **The GPV Step-2 per-slot front-loading joint coupling.**
  --
  -- This is the deferred-sampling content.  The left mass lives on the
  -- counter-augmented trap run `progGameRunImplCombinedTrapCount`: at the *adaptively-determined*
  -- `j`-th programming step, an inline uniform winner image `v⋆ ← $ᵗ Range` is drawn *inside* the
  -- `simulateQ` fold, cached at the forged point, and the write-only trapdoor preimage
  -- `trapdoorSample (pk, sk) v⋆` is recorded.  The right mass averages the embedded target
  -- `y ← $ᵗ Range` *outside* the fold and runs `embedTrapImpl … j y`, which caches `y` at its
  -- count-`j` random-oracle miss and draws fresh uniform images everywhere else.
  --
  -- **Fold the `y`-average into a single front draw.** The right-hand `∑' y`
  -- weighted by `Pr[= y | $ᵗ Range]` is exactly the output probability of the bind that draws
  -- `y ← $ᵗ Range` first and then runs the per-target win game (`probOutput_bind_eq_tsum`).  This
  -- puts the right side in the *front-loaded* form `Pr[= true | y ← $ᵗ Range; …]`, matching the
  -- trap run's inline `v⋆ ← $ᵗ Range` up to the adaptive count-`j` position.
  rw [← probOutput_bind_eq_tsum]
  -- **The adaptive count-`j` front-loading, via the front-draw lift.**
  --
  -- The goal is now `LHS_trap ≤ Pr[= true | y ← $ᵗ Range; x ← trapdoorSample pk sk y;
  --   r ← (simulateQ (embedTrapImpl … j y) (adv.main pk)).run (∅, 0);
  --   pure (decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y))]`, i.e. both sides now carry
  -- a single `$ᵗ Range` draw: the trap run draws it *inline* at the adaptively-determined `j`-th
  -- programming step, the embed game draws it at the *front* (consumed at its count-`j` miss).
  --
  -- The adaptive PMF×PMF run coupling — pushing the trap run's inline winner draw
  -- `v⋆ ← $ᵗ Range` to the front and re-expressing it as the embedded target `y ← $ᵗ Range` across
  -- the whole adaptive fold — is
  -- `evalDist_frontDraw_embedTrapImpl_eq_embedTrapFresh`: averaging the trap-sibling embed run over
  -- the external target draw equals the inline-fresh run `embedTrapFreshImpl` (an all-fresh-uniform
  -- lazy random oracle with counter).  Its winner step substitutes the front `y` for the inline
  -- fresh winner draw and uses post-winner coincidence
  -- (`evalDist_run_embedTrapImpl_eq_embedTrapFresh_of_lt`); its off-winner steps commute the front
  -- draw past `y`-independent steps (`embedTrapImpl_run_step_eq_embedTrapFresh`,
  -- `OracleComp.DeferredSampling.evalDist_bind_comm`).
  --
  -- **The win-event same-randomness coupling.**
  --
  -- The lift couples the *run* (the cache/counter marginal), but the embed win event still reads
  -- the front target `y` directly — `r.2.1 (forged) = some y` and
  -- `r.1.2.2 = x ← trapdoorSample pk sk y` — so the lift cannot fire while `y` lives in the event.
  -- On the winner-slot support the cache *pins* `y`: at slot `j` the trap-sibling caches exactly
  -- `y`, so `r.2.1 (forged) = some y` forces `y = cache(forged)` and
  -- `x ← trapdoorSample pk sk (cache(forged))`.  Eliminating the explicit `y` via this cache-pin
  -- (a marginal over `y` tied to the cache value) puts the embed win in run-only form, after which
  -- the front-draw lift rewrites the run to `embedTrapFreshImpl` and the
  -- trap-count run is its trapdoor-table/index augmentation (the LHS handler
  -- `progGameRunImplCombinedTrapCount` draws the *same* fresh `v` and records
  -- `table(forged) = trapdoorSample pk sk v` with `idx(forged) = some j`).  Matching the trap event
  -- `table(forged) = trapdoorSample (cache(forged))` to the embed event `output = trapdoorSample
  -- (cache(forged))` is the final N4-style same-randomness coupling
  -- (`evalDist_simulateQ_run_eq_of_impl_evalDist_eq` after projecting to the common
  -- `embedTrapFreshImpl` cache/counter state) and the trapdoor draw `x`.
  --
  -- **Commute the trapdoor draw `x` past the embed run.**  The trapdoor
  -- preimage `x ← trapdoorSample pk sk y` is drawn from an *independent* `ProbComp` (it does not
  -- feed the embed run `simulateQ (embedTrapImpl … j y)`, which consumes only `y`), so the two
  -- binds exchange at the distribution level (`OracleComp.DeferredSampling.evalDist_bind_comm`).
  -- Running the embed first and drawing `x` afterwards leaves the win event — and hence the output
  -- probability `Pr[= true | …]` — unchanged.  This re-expresses the right-hand game in the
  -- *run-first* form, in which the embed run output `r` is already available when the trapdoor draw
  -- `x` and the win predicate `decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y)` are
  -- evaluated.
  rw [show Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let x ← psf.trapdoorSample pk sk y
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)]
      = Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk y
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] from by
    refine probOutput_congr rfl ?_
    refine evalDist_bind_congr' _ (fun y => ?_)
    exact OracleComp.DeferredSampling.evalDist_bind_comm (psf.trapdoorSample pk sk y)
      ((simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run (∅, 0))
      (fun x r => pure (decide (r.1.2.2 = x) &&
        decide (r.2.1 (r.1.2.1, r.1.1) = some y)))]
  -- **Pin the trapdoor draw to the cached image at the forged point.**  The
  -- win predicate is `decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y)`; whenever its
  -- second conjunct holds the cached image at the forged point is exactly the front target,
  -- `r.2.1 (forged) = some y`, so `(r.2.1 (forged)).getD y = y` and the trapdoor preimage
  -- `x ← trapdoorSample pk sk y` equals `x ← trapdoorSample pk sk ((r.2.1 (forged)).getD y)`.
  -- When the second conjunct fails the whole `&&` is `false` regardless of `x`, so the trapdoor
  -- draw is irrelevant and either target yields the same (constant-`false`) win distribution.
  -- This pins the trapdoor draw to a *run-read* cache value — eliminating the free `y` from the
  -- trapdoor draw, leaving it only in the cache-comparison literal `some y`.
  rw [show Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk y
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)]
      = Pr[= true | (do
        let y ← ($ᵗ Range : ProbComp Range)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        let x ← psf.trapdoorSample pk sk ((r.2.1 (r.1.2.1, r.1.1)).getD y)
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] from by
    refine probOutput_congr rfl (evalDist_bind_congr' _ (fun y => ?_))
    refine evalDist_bind_congr' _ (fun r => ?_)
    rcases hc : r.2.1 (r.1.2.1, r.1.1) with _ | yv
    · simp only [Option.getD_none]
    · simp only [Option.getD_some]
      by_cases hy : yv = y
      · rw [hy]
      · simp only [Option.some.injEq, hy, decide_false, Bool.and_false]
        rw [OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
            ((hNF y).probFailure_eq_zero),
          OracleComp.DeferredSampling.evalDist_bind_const_neverFails _
            ((hNF yv).probFailure_eq_zero)]]
  -- **Index-augment the embed run and restrict the win to the winner slot.**
  -- The win predicate `decide (r.1.2.2 = x) && decide (r.2.1 (forged) = some y)` reads only the
  -- embed run *output* `r.1.2.2` and *cache* `r.2.1`, both of which are recovered from the
  -- index-augmented run `embedTrapIdxImpl … j y` by the passive projection
  -- `map_run_embedTrapIdxImpl_proj` (the inserted insertion-index table is never read).  Hence the
  -- right-hand win mass equals the same win mass on the augmented run, which dominates its
  -- restriction to the further conjunct `idx(forged) = some j` (the run-only winner-slot witness):
  --
  --   `RHS' := ∑'y Pr[=y] · Pr[= true | embedTrapIdxImpl … j y; x ← trapdoorSample (cache forged);
  --              pure (win ∧ idx(forged) = some j)]  ≤  RHS`.
  --
  -- This is the sound monotone reduction (`probOutput` over a conjoined Bool) that re-expresses the
  -- right side on the index-augmented run with the winner-slot restriction made explicit, so that
  -- the front target `y` enters only through run-only predicates (`idx(forged) = some j`) — exactly
  -- the form the trap-count run's `idx(forged) = some j` event couples to.
  refine le_trans ?_ (reservoir_embed_winnerIdx_le psf hr M Salt pk sk j adv)
  -- **The freshness-confined winner-slot coupling.**
  --
  -- Goal here (after the winner-idx monotone step `reservoir_embed_winnerIdx_le`):
  --   ⊢ Pr[fun w => ((fresh w.1.1 ∧ verify ∧ isShort) ∧ table(forged) = some w.1.2.2)
  --        ∧ idx(forged) = some j | (simulateQ progGameRunImplCombinedTrapCount (adv.main pk)).run]
  --     ≤ ∑'y Pr[= y | $ᵗ Range] ·
  --         Pr[= true | r ← (simulateQ (embedTrapIdxImpl … j y) (adv.main pk)).run ((∅, 0), ∅idx);
  --                     x ← trapdoorSample pk sk ((r.2.1.1 (forged)).getD y);
  --                     pure (decide (r.1.2.2 = x) && decide (r.2.1.1 (forged) = some y)
  --                            && decide (r.2.2 (forged) = some j))]
  --
  -- ⚠ The FRESHNESS conjunct `w.1.1 ∉ w.2.1.1.1.2` (`forged.msg ∉ signedSet`) is LOAD-BEARING and
  -- must NOT be dropped.  Dropping it makes the bound FALSE: both the trap run's signing branch
  -- (`progGameRunImplCombinedTrapCount_run_inr`) and the embed run's signing branch
  -- (`embedTrapIdxImpl_run_inr`) increment the counter and write the insertion-index table, but the
  -- embed's signing branch caches a *fresh* `c` (it never tests `j`), not the embedded `y`.  So a
  -- replay adversary making one signing query on `m` at counter `j`, receiving `(r, x =
  -- trapdoorSample c)` and outputting the forgery `(r, m, x)`, gives trap mass
  -- `table(forged) = some x ∧ idx(forged) = some j` with probability `1`, while the embed side
  -- needs the fresh `c = y` — a `1/|Range|` coincidence (witness: the bijective PSF, `j = 0`).
  --
  -- Route (freshness collapses the joint coupling to marginal + deterministic recovery): freshness
  -- ⟹ `forged.msg` was never signed ⟹ `forged` can only have been inserted by a random-oracle miss,
  -- at counter `j` (since `idx(forged) = some j`), where the embed caches exactly `y` — so on that
  -- slot the diagonal `cache(forged) = some y` is recovered from the run state, eliminating the
  -- free `y` from the embed win literal.  The marginal lift
  -- `evalDist_frontDraw_embedTrapIdxSigImpl_eq_embedTrapFreshSigImpl` then fires; the trap-count
  -- run is matched to `embedTrapFreshIdxSigImpl` by the freshness recovery
  -- `embedTrapIdxSigImpl_fresh_idx_cache_eq` and the write-only-table support invariant
  -- `progGameRunImplCombinedTrapCount_table_support`.  The omitted embed-side signing-slot mass on
  -- the right is nonnegative, so the bound is an inequality (trap ≤ embed), not an equality.
  --
  -- **The run-marginal half.** The cache/counter/idx/signedSet marginals of
  -- the trap-count run and the inline-fresh signed-set embed run coincide *as distributions*, via
  -- the generic `evalDist`-level state-projection transport
  -- `evalDist_map_run_simulateQ_eq_of_query_evalDist_map_eq` (which tolerates the never-failing
  -- answer-irrelevant trapdoor draw at each RO miss) instantiated as
  -- `map_run_progGameRunImplCombinedTrapCount_freshSig_proj`.  This discharges the *run-marginal*
  -- half of the coupling: it identifies the trap-count cache/idx/signedSet law with the
  -- `embedTrapFreshIdxSigImpl` law that the front-draw lift produces from
  -- `∑'y Pr[=y] · embedTrapIdxSigImpl … j y`.
  --
  -- **The table↔trapdoor-draw joint factorization.** On the
  -- trap run the forged point's write-only table entry `table(forged) = some preimg` was sampled
  -- `x ← trapdoorSample pk sk (cache(forged))` *inline* at the adaptively-determined forged
  -- programming event, and must be front-loaded to the embed side's *post-run* trapdoor draw
  -- `x ← trapdoorSample pk sk (cache(forged))`, matching the recorded `x` to the adversary output
  -- `preimg`.  FRESHNESS is exactly what makes this draw answer-irrelevant (an unsigned forged key
  -- is an RO miss, whose `x` enters only the write-only table — never the adversary view; a
  -- *signed* key returns `(r, x)` to the adversary, so its table draw is *not* deferrable, which is
  -- why dropping FRESH falsifies the bound).  Formalizing this defer-to-end of one
  -- answer-irrelevant write-only draw across the adaptive `simulateQ` fold is the genuine joint
  -- PMF×PMF coupling: a per-final-state induction (à la
  -- `tsum_probOutput_simulateQ_run_mul_of_rel`) showing the table at
  -- an unsigned key is an independent fresh `trapdoorSample (cache key)` conditioned on the final
  -- cache/idx/signedSet state, carried out in `trap_freshSig_le_winnerSlot_deferred`.
  --
  -- **Assembly.** Drop the verify/isShort conjuncts (they only restrict; FRESH stays) by
  -- `probEvent_mono`, then chain the trap-side table-defer
  -- `trap_freshSig_le_winnerSlot_deferred` (`G_trap ≤` the freshness-confined deferred functional
  -- expectation over the inline-fresh run) with the embed-side reduction
  -- `freshSig_winnerSlot_deferred_le_embed` (that expectation `≤` the winner-slot-restricted
  -- per-target embedding win).
  refine le_trans (probEvent_mono ?_)
    (le_trans (trap_freshSig_le_winnerSlot_deferred psf hr M Salt pk sk j adv hNF)
      (freshSig_winnerSlot_deferred_le_embed psf hr M Salt pk sk j adv))
  rintro w - ⟨⟨hflag, htbl⟩, hidx⟩
  refine ⟨⟨?_, htbl⟩, hidx⟩
  -- The flag conjunct `(decide fresh && (decide verify && isShort)) = true` carries the FRESH
  -- literal `forged.msg ∉ signedSet`, which is preserved verbatim.
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hflag
  exact hflag.1

open Classical in
omit [Fintype Salt] in
/-- **The per-slot front-loading deferred-sampling coupling (budget-scaled form).**

For a fixed programmed-entry index `j`, the *index-tagged* trap-exact-match mass — the trap event on
the counter-augmented run `progGameRunImplCombinedTrapCount` further restricted to the event that
the forged random-oracle point was *programmed at counter value `j`* (its recorded insertion index
is `some j`) — is bounded by the budget-scaled reservoir winner mass
`(qSign + qHash) · Pr[= some j | reservoirWinnerIndex (qSign + qHash)] · S (some j)` at slot `j`,
where `S (some j)` is the
winner-slot-restricted per-target embedding win of `embedTrapImpl … j y` averaged over `y ← $ᵗ
Range`.

This is derived from the floor-free form `reservoir_embed_commute_winner_floorFree` by the reservoir
arithmetic: at `j < qSign + qHash` the winner mass is exactly `(qSign + qHash)⁻¹`
(`probOutput_reservoirWinnerIndex_eq`), so `(qSign + qHash) · (qSign + qHash)⁻¹ = 1` absorbs the
budget factor and the floor-free bound passes through; at `j ≥ qSign + qHash` no programmed entry
can have recorded index `j` (`progGameRunImplCombinedTrapCount_idx_lt_budget`), so the left mass is
`0`.  The multi-target factor `qSign + qHash` pays the guessing loss. -/
lemma reservoir_embed_commute_winner [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) (j : ℕ) :
    Pr[fun w : (M × (Salt × Domain)) ×
          (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
            (((Salt × M) → Option ℕ) × ℕ)) =>
          ((decide (w.1.1 ∉ w.2.1.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
            w.2.2.1 (w.1.2.1, w.1.1) = some j |
        (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
          (adv.main pk)).run
          (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
            (fun _ => none), 0)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        Pr[= some j | reservoirWinnerIndex (qSign + qHash)] *
          ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x) &&
                decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  set Q := qSign + qHash with hQdef
  set S : ENNReal := ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk y
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk j y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] with hSdef
  set LHS : ENNReal := Pr[fun w : (M × (Salt × Domain)) ×
        (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
          (((Salt × M) → Option ℕ) × ℕ)) =>
        ((decide (w.1.1 ∉ w.2.1.1.1.2) &&
            (decide (psf.eval pk w.1.2.2 =
                (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
              psf.isShort w.1.2.2)) = true ∧
          w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2) ∧
          w.2.2.1 (w.1.2.1, w.1.1) = some j |
      (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
        (adv.main pk)).run
        (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
          (fun _ => none), 0)] with hLHSdef
  -- Floor-free per-slot bound (the genuine front-loading commute).
  have hfloorFree : LHS ≤ S :=
    reservoir_embed_commute_winner_floorFree psf hr M Salt domainSample pk sk qSign qHash adv
      hreg hNF hForge hQ j
  change LHS ≤ (Q : ENNReal) * Pr[= some j | reservoirWinnerIndex Q] * S
  by_cases hj : j < Q
  · -- Slot `j` is within budget: the winner mass is exactly `Q⁻¹`, so `Q · Q⁻¹ = 1` absorbs the
    -- budget factor and the floor-free bound passes through.
    have hres : Pr[= some j | reservoirWinnerIndex Q] = (Q : ℝ≥0∞)⁻¹ :=
      probOutput_reservoirWinnerIndex_eq Q j hj
    rw [hres]
    have hQne : (Q : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]; omega
    have hQtop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
    rw [ENNReal.mul_inv_cancel hQne hQtop, one_mul]
    exact hfloorFree
  · -- Slot `j` is beyond budget: no programmed entry has recorded index `j`, so `LHS = 0`.
    have hLHS0 : LHS = 0 := by
      rw [hLHSdef]
      refine probEvent_eq_zero ?_
      intro w hmem hP
      have hidxlt := progGameRunImplCombinedTrapCount_idx_lt_budget psf M Salt pk sk qSign qHash
        (adv.main pk) hQ hmem hP.2
      omega
    rw [hLHS0]
    exact zero_le'

open Classical in
omit [Fintype Salt] in
/-- **M3, index-restricted: the reservoir↔embedding coupling (single fold-commute core).**

This is the deferred-sampling coupling of the GPV Step-2 exact-match close, with the
winner-slot bookkeeping made explicit: the per-target embedding win on the right is *restricted* to
the event that the **forged random-oracle point is the embedded (winner) slot**, read off the embed
final state as `r.2.1 (r.1.2.1, r.1.1) = some y` — at slot `wOpt.getD (qSign + qHash)` the
trap-sibling handler `embedTrapImpl` caches exactly the external target `y` at the winner
random-oracle miss, so the forged point being the winner slot is precisely its cached image being
`y`.

`reservoir_embed_commute` (M3) follows from this restricted form by dropping the winner-slot
restriction (`probOutput` monotonicity over the conjoined Bool): the *full* per-target win is at
least the winner-slot-restricted win, so the M3 bound is implied by the present, tighter bound.
Stating the restriction here lets the reservoir arithmetic (`probOutput_reservoirWinnerIndex_ge`,
the budget `N ≤ qSign + qHash` of `embedAtIndexImpl_run_count_le_budget` /
`combined_run_table_card_le`) be carried at the index-tagged level, while the per-winner-slot
front-loading joint coupling — pushing the trap run's inline winner draw `v⋆ ← $ᵗ Range` to the
front and re-expressing it as the embedded target `y ← $ᵗ Range` (mirroring
`evalDist_gpvRealImpl_eq_drawList_gpvRealImplTape`), together with the realized-entry index
partition of the trap mass — is supplied by `reservoir_embed_commute_winner`.

The bound holds for the same reason as M3: after the write-only-table deferral both runs maintain an
all-uniform random-oracle cache, and *averaging* the embedded target `y` over `$ᵗ Range`
reconstitutes the trap run's inline uniform winner draw `v⋆`.  The winner-slot-equals-forged-slot
contribution, summed over the `N ≤ qSign + qHash` realized programmed entries with per-slot
reservoir mass `1 / N ≥ 1 / (qSign + qHash)` and multiplied by `qSign + qHash`, already recovers the
full trap mass.  Trap-side index bookkeeping and the per-slot fold-commute supply the remaining
content. -/
lemma reservoir_embed_commute_residual [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
          (decide (w.1.1 ∉ w.2.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
        (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk)
          (adv.main pk)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
          ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                  (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x) &&
                decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] := by
  -- Abbreviations: `Q` the multi-target budget, `S wOpt` the per-slot averaged restricted embedding
  -- win, `trap` the LHS trap-exact-match mass.
  set Q := qSign + qHash with hQdef
  set S : Option ℕ → ENNReal := fun wOpt =>
    ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk y
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk (wOpt.getD Q) y) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x) &&
          decide (r.2.1 (r.1.2.1, r.1.1) = some y)) : ProbComp Bool)] with hSdef
  set trap : ENNReal := Pr[fun w : (M × (Salt × Domain)) ×
        ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
        (decide (w.1.1 ∉ w.2.1.1.2) &&
            (decide (psf.eval pk w.1.2.2 =
                (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
              psf.isShort w.1.2.2)) = true ∧
          w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
      (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk)
        (adv.main pk)).run
        ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
    with htrapdef
  change trap ≤ (Q : ENNReal) * ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex Q] * S wOpt
  -- **Per-slot index partition + commute.**  The per-entry mass function `g : ℕ → ENNReal` is the
  -- index-tagged trap-exact-match mass on the counter-augmented run
  -- `progGameRunImplCombinedTrapCount`, restricted to the event that the forged point was
  -- programmed at counter value `j`.  Summing `g j` over `j` recovers the full trap mass: the
  -- instrument is passive (`map_run_progGameRunImplCombinedTrapCount_proj`), so the augmented
  -- trap-event mass equals `trap`; and on every positive-probability trap outcome the forged
  -- point — being in the preimage table — has a recorded insertion index
  -- (`progGameRunImplCombinedTrapCount_idx_iff_table`), so the deterministic-index partition
  -- (`probEvent_eq_tsum_probEvent_index_aux`) tiles the trap mass over the recorded indices.  The
  -- per-slot domination `g j ≤ Q · Pr[= some j] · S` is the per-slot front-loading commute
  -- (`reservoir_embed_commute_winner`).
  obtain ⟨g, hgsum, hgle⟩ : ∃ g : ℕ → ENNReal,
      (∑' j : ℕ, g j) = trap ∧
      ∀ j : ℕ, g j ≤ (Q : ENNReal) * Pr[= some j | reservoirWinnerIndex Q] * S (some j) := by
    -- The counter-augmented run started from the projected empty state.
    set augRun := (simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk)
        (adv.main pk)).run
        (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none),
          (fun _ => none), 0) with hAugRun
    -- The trap event lifted to the augmented state (referencing only the trap-state component).
    set Paug : (M × (Salt × Domain)) ×
        (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
          (((Salt × M) → Option ℕ) × ℕ)) → Prop := fun w =>
        (decide (w.1.1 ∉ w.2.1.1.1.2) &&
            (decide (psf.eval pk w.1.2.2 =
                (w.2.1.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
              psf.isShort w.1.2.2)) = true ∧
          w.2.1.2 (w.1.2.1, w.1.1) = some w.1.2.2 with hPaug
    -- The forged-point recorded insertion index, read off the augmented final state.
    set idx : (M × (Salt × Domain)) ×
        (((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
          (((Salt × M) → Option ℕ) × ℕ)) → Option ℕ := fun w =>
        w.2.2.1 (w.1.2.1, w.1.1) with hIdx
    refine ⟨fun j => Pr[fun w => Paug w ∧ idx w = some j | augRun], ?_, ?_⟩
    · -- Partition: `∑' j, g j = trap`.
      -- The augmentation is passive, so the augmented trap-event mass equals `trap`.
      have htrap_eq : trap = Pr[Paug | augRun] := by
        rw [htrapdef, ← map_run_progGameRunImplCombinedTrapCount_proj psf M Salt pk sk
          (adv.main pk) (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
            fun _ => none), (fun _ => none), 0), probEvent_map]
        rfl
      rw [htrap_eq]
      -- Every positive-probability trap outcome has a recorded forged-point index.
      refine (probEvent_eq_tsum_probEvent_index_aux augRun Paug idx ?_).symm
      intro w hw hPw
      have hmem : w ∈ support augRun := by
        by_contra hns
        exact hw (probOutput_eq_zero_of_not_mem_support hns)
      have hinv := progGameRunImplCombinedTrapCount_idx_iff_table psf M Salt pk sk
        (adv.main pk) (((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false),
          fun _ => none), (fun _ => none), 0) (by intro k; simp) w hmem (w.1.2.1, w.1.1)
      rw [hIdx]
      exact (hinv.mp (by rw [hPaug] at hPw; rw [hPw.2]; exact Option.some_ne_none _))
    · -- Per-slot domination: the per-slot front-loading commute.
      intro j
      exact reservoir_embed_commute_winner psf hr M Salt domainSample pk sk qSign qHash
        adv hreg hNF hForge hQ j
  -- **Reservoir arithmetic.**  Push the budget factor `Q` through the winner sum and bound
  -- the trap partition `g` by the `some j` atoms of the reservoir winner average, discarding the
  -- never-firing `none` atom (`tsum_option`, terms nonnegative).
  calc trap = ∑' j : ℕ, g j := hgsum.symm
    _ ≤ ∑' j : ℕ, (Q : ENNReal) * Pr[= some j | reservoirWinnerIndex Q] * S (some j) :=
        ENNReal.tsum_le_tsum hgle
    _ = ∑' j : ℕ, (Q : ENNReal) * (Pr[= some j | reservoirWinnerIndex Q] * S (some j)) := by
        simp_rw [mul_assoc]
    _ ≤ (Q : ENNReal) *
        ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex Q] * S wOpt := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        rw [tsum_option _ ENNReal.summable]
        exact le_add_self

open Classical in
omit [Fintype Salt] in
/-- **M3 — the GPV Step-2 reservoir↔embedding deferred-sampling coupling.**

This is the joint coupling of the GPV Step-2 exact-match close, stated as the
*bound* needed by `gpv_perKey_exactMatch_le_reservoir`.  The left-hand side is the exact-match
winning mass of the trapdoor-recording combined run `progGameRunImplCombinedTrap` — the run obtained
from the combined sign-then-hash game after the write-only-table deferral (Lemma A,
`evalDist_run_progGameRunImplCombinedTrap_eq`).  The right-hand side is the multi-target factor
`qSign + qHash` times the full programmed-preimage reduction win, averaged over the reservoir winner
slot `wOpt ← reservoirWinnerIndex (qSign + qHash)` and the uniform target `y ← $ᵗ Range`: for each
slot/target the reduction runs the adversary under the all-uniform-cache trap-sibling embedding
handler `embedTrapImpl … (wOpt.getD (qSign + qHash)) y`, embeds the external challenge `y` at slot
`wOpt`, and wins when its forged preimage `r.1.2.2` equals the challenger's trapdoor preimage
`x ← trapdoorSample pk sk y`.

The bound holds because, after the write-only-table deferral, both runs maintain an all-uniform
random-oracle cache, and *averaging* the embedded target `y` over `$ᵗ Range` reconstitutes the
trap run's inline uniform winner draw `v⋆ ← $ᵗ Range`; the trap run's write-only
`table(forged) = trapdoorSample (cache(forged))` is then an independent fresh preimage that couples
to the reduction's external `x ~ trapdoorSample y` exactly when the winner slot is the forged point
(`cache(forged) = v⋆ ≡ y`).  The winner-slot-equals-forged-slot contribution, summed over the `N`
realized programmed entries with per-slot reservoir mass `1 / N` and multiplied by `qSign + qHash`
(with `N ≤ qSign + qHash`, `combined_run_table_card_le`), already recovers the full trap mass; the
reduction wins on *additional* coincidence paths (the forged slot differs from the embedded slot yet
its cached image coincides with `y`), so the inequality is one-directional (`≤`), not an equality.
The form is correct at `qSign + qHash = 0` (both sides vanish: no programmed entry is recorded, so
the trap mass is zero).

This is the deferred-sampling coupling where the `y`-draw lives *outside* the
`simulateQ` fold while `v⋆` lives *inside* it at an adaptively-determined fold position; the
front-loading joint-coupling is the core content of the GPV Step-2 close. -/
lemma reservoir_embed_commute [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun w : (M × (Salt × Domain)) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
          (decide (w.1.1 ∉ w.2.1.1.2) &&
              (decide (psf.eval pk w.1.2.2 =
                  (w.2.1.1.1 (w.1.2.1, w.1.1)).getD (psf.eval pk w.1.2.2)) &&
                psf.isShort w.1.2.2)) = true ∧
            w.2.2 (w.1.2.1, w.1.1) = some w.1.2.2 |
        (simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk)
          (adv.main pk)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
          ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
            Pr[= true | (do
              let x ← psf.trapdoorSample pk sk y
              let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                  (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
                ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
              pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
  -- M3 from the index-restricted form: bound the trap mass by the winner-slot-restricted RHS
  -- (`reservoir_embed_commute_residual`), then drop the winner-slot restriction
  -- `&& decide (… = some y)` from every per-target win (full win ≥ the restricted win).
  refine le_trans (reservoir_embed_commute_residual psf hr M Salt domainSample pk sk qSign qHash
    adv hreg hNF hForge hQ) ?_
  gcongr ((qSign + qHash : ℕ) : ENNReal) *
    ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
      ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] * ?_ with wOpt y
  -- Per-target: dropping the conjunct `decide (r.2.1 (r.1.2.1, r.1.1) = some y)` only increases
  -- the winning mass (`probOutput` monotone over the conjoined Bool body).
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => ?_
  gcongr
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun r => ?_
  gcongr
  rw [probOutput_pure, probOutput_pure]
  by_cases hxr : r.1.2.2 = x
  · simp only [hxr, decide_true, Bool.true_and]
    split <;> simp
  · simp [hxr]

open Classical in
omit [Fintype Salt] in
/-- **Exact-match reservoir bound (Step-2 exact-match branch).** The exact-match winning mass on the
combined verify-extended run — a verifying fresh forgery `(msg, (r, s⋆))` whose forged preimage `s⋆`
exactly reproduces the simulator's hidden programmed preimage `sHidden` recorded in the table at the
forged point — is bounded by the multi-target factor `qSign + qHash` times the exact-match
programmed preimage advantage of `programmedPreimageReduction` at `(pk, sk)`.

The programmed-preimage reduction embeds its uniform target `y` at one uniformly chosen programmed
entry (reservoir sampling over the at most `qSign + qHash` programmed random-oracle entries); when
the embedded entry is the forged point and the forgery reproduces the hidden preimage, it wins the
single-target programmed-preimage experiment, paying the explicit `qSign + qHash` guessing loss.

This is the exact-match branch of the GPV Step-2 collision extraction; the
distinct-preimage branch is discharged by `gpv_perKey_distinct_le_collision`. -/
lemma gpv_perKey_exactMatch_le_reservoir [DecidableEq Domain] [Inhabited Range]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hreg : 𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
            (decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2 |
        (simulateQ (progGameRunImplCombined psf M Salt domainSample pk)
          (adv.main pk >>= fun out => (fun v => (out, v)) <$> gpvVerifyRead psf M Salt pk out)).run
          ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none)]
      ≤ ((qSign + qHash : ℕ) : ENNReal) *
        Pr[= true | (do
          let y ← ($ᵗ Range : ProbComp Range)
          let x ← psf.trapdoorSample pk sk y
          let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
          pure (decide (x' = x)) : ProbComp Bool)] := by
  -- **Step A (verify-strip, reduction-agnostic).**  Strip the verify continuation: on the forced
  -- cache hit at the forged point the verification read is table-passive, so the verify-extended
  -- exact-match mass is bounded by the exact-match event on `adv.main pk`'s combined run alone.
  refine le_trans
    (gpv_perKey_exactMatch_verifyStrip_le psf hr M Salt domainSample pk adv hForge) ?_
  -- **Step B (target factorization).**  Expand the reduction's averaged exact-match advantage over
  -- the uniform target draw `y ← $ᵗ Range` and push the `(qSign + qHash)` factor inside the sum, so
  -- the goal becomes the verify-stripped LHS bounded by
  --   `∑' y, (qSign + qHash) * (Pr[= y | $ᵗ Range] * Pr[per-y exact-match win])`.
  rw [programmedPreimage_perKey_eq_tsum psf hr M Salt domainSample pk sk qSign qHash adv,
    ← ENNReal.tsum_mul_left]
  -- **N4 rewrite.**  Inside every per-target factor `P_y`, replace the pre-sampled-index
  -- handler `embedAtIndexImpl` by its trapdoor-uniform sibling `embedTrapImpl` (N4); after this the
  -- embed run has an all-uniform cache (modulo `y` at the winner slot), matching the cache marginal
  -- of the trapdoor-recording combined run.
  have hN4 : ∀ y : Range,
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk y
        let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
        pure (decide (x' = x)) : ProbComp Bool)]
      = Pr[= true | (do
          let x ← psf.trapdoorSample pk sk y
          let wOpt ← reservoirWinnerIndex (qSign + qHash)
          let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
              (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
          pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
    intro y
    refine probOutput_congr rfl ?_
    simp only [programmedPreimageReduction_eq_run, bind_assoc, pure_bind]
    refine evalDist_bind_congr fun x _ => ?_
    refine evalDist_bind_congr fun wOpt _ => ?_
    -- The remaining `run >>= pure ∘ decide` factor is equidistributed under N4.
    rw [evalDist_bind, evalDist_bind,
      evalDist_run_embedAtIndexImpl_eq_embedTrap psf M Salt domainSample pk sk
        (wOpt.getD (qSign + qHash)) y hreg hNF (adv.main pk)
        ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))]
  -- **N4 applied.**  Replace every per-target embed run by its all-uniform-cache trap
  -- sibling `embedTrapImpl`, so the goal RHS is the reservoir/target average of the *trap-sibling*
  -- embedding run, matching the cache marginal of the trapdoor-recording combined run.
  simp only [hN4]
  -- **M1 (Lemma A — write-only-table deferral).**  Push the verify-stripped LHS exact-match mass
  -- off the eval-caching combined run `progGameRunImplCombined` onto its trapdoor-recording sibling
  -- `progGameRunImplCombinedTrap`, an exact equidistribution under `hreg` with the event unchanged.
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_run_progGameRunImplCombinedTrap_eq psf M Salt domainSample pk sk hreg (adv.main pk)
      ((((∅ : (Salt × M →ₒ Range).QueryCache), (∅ : Finset M)), false), fun _ => none))]
  -- **M4 (assembly).**  Pull the reservoir winner draw `wOpt` to the front of each per-target win,
  -- swap the target/reservoir averages, fold in the multi-target factor, and discharge the result
  -- against the reservoir↔embedding coupling `reservoir_embed_commute` (M3).
  have hpull : ∀ i : Range,
      Pr[= true | (do
        let x ← psf.trapdoorSample pk sk i
        let wOpt ← reservoirWinnerIndex (qSign + qHash)
        let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
            (wOpt.getD (qSign + qHash)) i) (adv.main pk)).run
          ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
        pure (decide (r.1.2.2 = x)) : ProbComp Bool)]
      = ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
        Pr[= true | (do
          let x ← psf.trapdoorSample pk sk i
          let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
              (wOpt.getD (qSign + qHash)) i) (adv.main pk)).run
            ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
          pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
    intro i
    rw [probOutput_bind_eq_tsum]
    simp_rw [probOutput_bind_eq_tsum (reservoirWinnerIndex (qSign + qHash)),
      probOutput_bind_eq_tsum (psf.trapdoorSample pk sk i), ← ENNReal.tsum_mul_left, ← mul_assoc]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun wOpt => tsum_congr fun x => by ring
  -- Reassociate the per-target sum into the multi-target factor times the reservoir/target average
  -- that `reservoir_embed_commute` equates to the trap exact-match mass.
  have hrhs :
      (∑' i : Range, ((qSign + qHash : ℕ) : ENNReal) *
          (Pr[= i | ($ᵗ Range : ProbComp Range)] *
            ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
              Pr[= true | (do
                let x ← psf.trapdoorSample pk sk i
                let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                    (wOpt.getD (qSign + qHash)) i) (adv.main pk)).run
                  ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
                pure (decide (r.1.2.2 = x)) : ProbComp Bool)]))
        = ((qSign + qHash : ℕ) : ENNReal) *
          ∑' wOpt : Option ℕ, Pr[= wOpt | reservoirWinnerIndex (qSign + qHash)] *
            ∑' y : Range, Pr[= y | ($ᵗ Range : ProbComp Range)] *
              Pr[= true | (do
                let x ← psf.trapdoorSample pk sk y
                let r ← (simulateQ (embedTrapImpl psf M Salt pk sk
                    (wOpt.getD (qSign + qHash)) y) (adv.main pk)).run
                  ((∅ : (Salt × M →ₒ Range).QueryCache), (0 : ℕ))
                pure (decide (r.1.2.2 = x)) : ProbComp Bool)] := by
    rw [← ENNReal.tsum_mul_left]
    simp_rw [← ENNReal.tsum_mul_left, ← mul_assoc]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun wOpt => tsum_congr fun y => by ring
  simp_rw [hpull]
  rw [hrhs]
  exact reservoir_embed_commute psf hr M Salt domainSample pk sk qSign qHash adv hreg hNF
    hForge hQ

open Classical in
omit [Fintype Salt] in
/-- **Step 2 (collision extraction): the keygen-averaged programmed freshness verify-Bool game is
bounded by the collision and exact-match reduction advantages.**

In the programmed sign-then-hash game `progGameVerifyFresh`, every random-oracle entry was
programmed as `psf.eval pk s` for a hidden short preimage `s ← domainSample pk`.  Under `hForge` the
forgery `(msg, (r, s⋆))` lands on a programmed entry, so the verification read is a cache hit
returning `psf.eval pk sHidden` for the simulator's hidden preimage `sHidden` at `(r, msg)`; a
verifying fresh forgery therefore satisfies `psf.eval pk s⋆ = psf.eval pk sHidden` with both
preimages short (the forged one by the verifier's `isShort` check, the hidden one by `hcorrect` and
`hreg`).  This splits into:

* the **distinct-preimage branch** `sHidden ≠ s⋆`, a collision under `psf.eval` extracted by the
  collision reduction `reduction` (which records the hidden preimage at each programmed point and
  returns `(sHidden, s⋆)`), bounding that mass by `collisionFindingAdvantage (reduction …)`; and
* the **exact-match branch** `sHidden = s⋆`, where the forgery reproduces the simulator's hidden
  preimage; the programmed-preimage reduction `programmedPreimageReduction` embeds its target `y` at
  one uniformly chosen programmed entry (reservoir sampling over the at most `qSign + qHash`
  entries), winning when the embedded entry is the forged point, which costs the explicit
  multi-target factor `qSign + qHash`.

This is the Step-2 collision extraction of the GPV proof, stated pinned over the concrete
programmed forgery game and the concrete reductions. -/
theorem gpv_progGameVerifyFreshAvg_le_collisionAdv_add_preimageAdv [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    Pr[= true | (𝒟[hr.gen] : SPMF (PK × SK)) >>= fun pksk =>
        progGameVerifyFresh psf hr M Salt adv domainSample pksk.1]
      ≤ collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) := by
  classical
  -- Reduce the keygen-average to a per-key `(pk, sk)` bound via the averaging skeleton SL-A,
  -- then discharge that per-key bound (the distinct-collision transfer + the reservoir exact-match
  -- bound) — the Step-2 collision extraction.
  refine gpv_progGameVerifyFreshAvg_le_of_perKey psf hr M Salt qSign qHash adv domainSample ?_
  intro pksk hmem
  -- Lift the game success onto the combined run, split into the distinct and exact-match branches,
  -- transfer the distinct branch to the collision reduction, and hand the exact branch to the
  -- reservoir bound.
  rw [progGameVerifyFresh_eq_probEvent_combined psf hr M Salt domainSample pksk.1 adv,
    reduction_collision_eq_probEvent_combined psf hr M Salt domainSample pksk.1 adv]
  refine le_trans (probEvent_mono (fun w _ hw => ?_) :
      _ ≤ Pr[fun w : ((M × (Salt × Domain)) × Bool) ×
          ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) =>
          ((decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) ≠ some w.1.1.2.2) ∨
            ((decide (w.1.1.1 ∉ w.2.1.1.2) && w.1.2) = true ∧
              w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2) | _]) ?_
  · by_cases heq : w.2.2 (w.1.1.2.1, w.1.1.1) = some w.1.1.2.2
    · exact Or.inr ⟨hw, heq⟩
    · exact Or.inl ⟨hw, heq⟩
  refine le_trans (probEvent_or_le _ _ _) ?_
  gcongr
  · exact gpv_perKey_distinct_le_collision psf hr M Salt domainSample pksk.1 pksk.2
      (hcorrect pksk.1 pksk.2 hmem) (hreg pksk.1 pksk.2 hmem) adv hForge
  · exact gpv_perKey_exactMatch_le_reservoir psf hr M Salt domainSample pksk.1 pksk.2 qSign qHash
      adv (hreg pksk.1 pksk.2 hmem) (hNF pksk.1 pksk.2 hmem) hForge (hQ pksk.1)

/-- **Full split GPV game-hop**: every successful fresh forgery falls into one of two cases.

1. **Distinct-preimage branch:** the forgery differs from the simulator's hidden programmed
   preimage at the forged point, yielding a collision under `psf.eval`.
2. **Exact-match branch:** the forgery exactly reproduces the simulator's hidden programmed
   preimage at that point. To capture this branch, the reduction guesses one of the at most
   `qSign + qHash` programmed entries and turns success there into a win in the single-target
   programmed-preimage experiment.

The only additional failure mode is a salt collision, bounded by `collisionBound`.

The honest trapdoor sampler is assumed total (`hNF`): for every key pair and target the sampler
`psf.trapdoorSample` never fails (`NeverFail`).  This is the standard GPV08 well-formedness
condition that the trapdoor inversion is a genuine distribution; it is the hypothesis that keeps
probability mass during the real↔programmed sign-then-hash hop and is not implied by `hcorrect`
(which constrains only the *support* of the sampler) nor by `hreg` (which equates only the *total
masses* of the two joint distributions).

The forger is assumed to query its forgery point (`hForge`, `ForgesQueriedPoint`): the standard
ROM well-formedness condition that the forgery lands on a programmed random-oracle entry, so the
collision/exact-match extraction observes the simulator's hidden preimage at that point. -/
theorem forgery_yields_collision_or_exact_match [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    adv.advantage (runtime M Salt) ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) *
          programmedPreimageAdvantage (psf := psf) (hr := hr)
            (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) +
        collisionBound Salt qSign qHash := by
  refine le_trans (gpv_advantage_le_progGameVerifyFreshAvg_add_collisionBound psf hr M Salt
    qSign qHash adv domainSample hreg hNF hQ) ?_
  gcongr
  exact gpv_progGameVerifyFreshAvg_le_collisionAdv_add_preimageAdv psf hr M Salt
    hcorrect qSign qHash adv domainSample hreg hNF hForge hQ

/-- **Collision-only specialization of the GPV split bound under a PSF preimage min-entropy
bound.**  This is `forgery_yields_collision_or_exact_match` with the exact-match
(programmed-preimage) branch controlled by an explicit preimage min-entropy / one-wayness bound
`εpp`: the adversary's chance of reproducing the simulator's hidden short preimage at a programmed
point is at most `εpp` (`hMinEntropy`), so the multi-target exact-match contribution is at most
`(qSign + qHash) · εpp`.  It is *derived* from the split bound and carries no independent proof
obligation.

The exact-match term is *bounded*, not eliminated: `programmedPreimageAdvantage ≥ 1 / |Domain| > 0`
for a finite domain (reproducing a sampled preimage is always possible with nonzero probability),
so a clean collision-only bound (`εpp = 0`) is unsatisfiable.  Specializing `εpp` to a concrete PSF
preimage min-entropy bound (e.g. for Falcon) yields the quantitative collision bound. -/
theorem forgery_yields_collision [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk) (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (domainSample : PK → ProbComp Domain)
    (hreg : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ForgesQueriedPoint psf hr M Salt adv domainSample)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (εpp : ℝ≥0∞)
    (hMinEntropy : programmedPreimageAdvantage (psf := psf) (hr := hr)
      (programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash) ≤ εpp) :
    adv.advantage (runtime M Salt) ≤
      collisionFindingAdvantage (psf := psf) (hr := hr)
          (reduction psf hr M Salt adv domainSample) +
        ((qSign + qHash : ℕ) : ENNReal) * εpp +
        collisionBound Salt qSign qHash := by
  refine le_trans (forgery_yields_collision_or_exact_match psf hr M Salt hcorrect qSign qHash
    adv domainSample hreg hNF hForge hQ) ?_
  gcongr

/-- **Collision-style GPV PFDH bound in the random-oracle model, under a preimage min-entropy
bound**.

For any adversary `A` making at most `qSign` signing queries against the GPV hash-and-sign
scheme with a correct PSF and `k`-bit salts, and making at most `qHash` random-oracle queries,
there exists a collision-finding reduction `B` such that:

  `Adv^{EUF-CMA}(A) ≤ Adv^{collision}(B) + (qSign + qHash) · εpp + (qSign + qHash)² / (2 · |Salt|)`

where `εpp` bounds the exact-match (programmed-preimage) branch: the chance that an adversary
reproduces the simulator's hidden short preimage at a programmed point is at most `εpp`
(`hMinEntropy`), the PSF preimage min-entropy / one-wayness assumption. The distinct-preimage
branch gives the collision term; the exact-match branch the `(qSign + qHash) · εpp` term. This is a
specialization of `euf_cma_split_bound` and is derived from it; the exact-match term is *bounded*,
not dropped, since `programmedPreimageAdvantage ≥ 1 / |Domain| > 0` for a finite domain.

The salt-collision term `(qSign + qHash)² / (2 · |Salt|)` is the birthday bound on a fresh
signing salt colliding with any previously recorded `(salt, message)` random-oracle input (a
prior signing salt or an adversary hash query). For Falcon with 40-byte salts
(`|Salt| = 2^320`), this is `2^{-191}` even for `qSign = qHash = 2^64`.

References: GPV08 Section 6; BDF+11 for the QROM extension. -/
theorem euf_cma_collision_bound [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk)
    (hreg : ∃ domainSample : PK → ProbComp Domain, ∀ (pk : PK) (sk : SK),
      (pk, sk) ∈ support hr.gen →
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ∀ ds : PK → ProbComp Domain, ForgesQueriedPoint psf hr M Salt adv ds)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash))
    (εpp : ℝ≥0∞)
    (hMinEntropy : ∀ ds : PK → ProbComp Domain,
      programmedPreimageAdvantage (psf := psf) (hr := hr)
        (programmedPreimageReduction psf hr M Salt adv ds qSign qHash) ≤ εpp) :
    ∃ (red : CollisionAdversary (PK := PK) (Domain := Domain)),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) red +
        ((qSign + qHash : ℕ) : ENNReal) * εpp +
        collisionBound Salt qSign qHash := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨reduction psf hr M Salt adv domainSample,
    forgery_yields_collision psf hr M Salt hcorrect qSign qHash adv domainSample h hNF
      (hForge domainSample) hQ εpp (hMinEntropy domainSample)⟩

/-- **Split GPV PFDH bound in the random-oracle model**.

This theorem makes both branches of the GPV proof explicit:

- a collision term for the distinct-preimage branch,
- a programmed-preimage replay term for the exact-match branch, with the explicit
  multi-target factor `qSign + qHash`,
- and the birthday salt-collision term.

It is the most honest generic statement available from the current API, before any additional
PSF-specific min-entropy lemma collapses the exact-match branch into the collision branch. -/
theorem euf_cma_split_bound [DecidableEq Domain]
    [Inhabited Range] [Nonempty Salt]
    (hcorrect : ∀ pk sk, (pk, sk) ∈ support hr.gen → psf.CorrectAt pk sk)
    (hreg : ∃ domainSample : PK → ProbComp Domain, ∀ (pk : PK) (sk : SK),
      (pk, sk) ∈ support hr.gen →
      𝒟[(do let s ← domainSample pk; pure (psf.eval pk s, s) : ProbComp (Range × Domain))] =
      𝒟[(do let c ← ($ᵗ Range); let s ← psf.trapdoorSample pk sk c; pure (c, s)
            : ProbComp (Range × Domain))])
    (qSign qHash : ℕ)
    (adv : SignatureAlg.unforgeableAdv
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt))
    (hNF : ∀ (pk : PK) (sk : SK), (pk, sk) ∈ support hr.gen →
      ∀ (c : Range), NeverFail (psf.trapdoorSample pk sk c))
    (hForge : ∀ ds : PK → ProbComp Domain, ForgesQueriedPoint psf hr M Salt adv ds)
    (hQ : ∀ pk, signHashQueryBound
      (S' := Salt × Domain) (α := M × (Salt × Domain))
      (oa := adv.main pk) (qSign := qSign) (qHash := qHash)) :
    ∃ (collisionRed : CollisionAdversary (PK := PK) (Domain := Domain))
      (exactMatchRed : ProgrammedPreimageAdversary
        (PK := PK) (Domain := Domain) (Range := Range)),
      adv.advantage (runtime M Salt) ≤
        collisionFindingAdvantage (psf := psf) (hr := hr) collisionRed +
          ((qSign + qHash : ℕ) : ENNReal) *
            programmedPreimageAdvantage (psf := psf) (hr := hr) exactMatchRed +
          collisionBound Salt qSign qHash := by
  obtain ⟨domainSample, h⟩ := hreg
  exact ⟨reduction psf hr M Salt adv domainSample,
    programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash,
    forgery_yields_collision_or_exact_match psf hr M Salt hcorrect qSign qHash adv
      domainSample h hNF (hForge domainSample) hQ⟩

end GPVHashAndSign
