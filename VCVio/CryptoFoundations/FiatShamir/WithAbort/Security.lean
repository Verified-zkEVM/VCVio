/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.CryptoFoundations.FiatShamir.WithAbort.GhostBodies
import VCVio.CryptoFoundations.FiatShamir.QueryBounds
import VCVio.ProgramLogic.Relational.SimulateQ
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import VCVio.OracleComp.QueryTracking.RandomOracle.ProbeEps
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# EUF-CMA security of Fiat-Shamir with aborts

Statistical CMA-to-NMA reduction for the Fiat-Shamir-with-aborts transform,
following Theorem 3 of Barbosa et al. (CRYPTO 2023, ePrint 2023/246).
Instantiates `FiatShamir.signHashQueryBound` at the with-aborts signature type
and exposes `cmaToNmaLoss` plus `euf_cma_to_nma` (the managed-RO NMA interface),
together with the hybrid game chain (`hybridExpAtKey` over the signing bodies
`realSignBody`, `progSignBody`, `transSignBody`, `simSignBody`) that structures
the proof.

The quantitative parameters `ε` (per-key commitment-guessing probability),
`p_abort` (per-attempt abort probability), and `δ` (key-regularity failure
probability) are tied to the identification scheme by explicit hypotheses on a
"good key" event, mirroring the event `Γ` of the paper's Lemma 1: `δ` bounds
the probability that key generation falls outside the event, and `ε`/`p_abort`
bound the per-key quantities pointwise on it.

The scheme-specific NMA-to-hard-problem reduction lives with each concrete
scheme (e.g. `MLDSA.nma_security`).
-/

universe u v

open OracleComp OracleSpec
open scoped BigOperators ENNReal

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

/-- The classical ROM statistical loss of the Fiat-Shamir-with-aborts CMA-to-NMA
reduction (after Theorem 3, CRYPTO 2023), for a per-attempt HVZK simulator:

`L = 2·qS·(qH+1)·ε/(1-p) + qS·ε·(qS+1)/(2·(1-p)²) + qS·ζ_zk/(1-p) + δ`

where:
- `qS` / `qH`: signing-oracle / adversarial random-oracle query bounds;
- `ε`: per-key commitment-guessing probability bound (on good keys);
- `p`: per-key, per-attempt abort probability bound (on good keys), for both the honest
  prover and the simulator;
- `ζ_zk`: total-variation error of the HVZK simulator for one signing **attempt**, over
  optional transcripts (`none` = abort), as in `IdenSchemeWithAbort.HVZK`;
- `δ`: probability that key generation falls outside the good-key event.

The first term pays for reprogramming collisions with adversarial hash queries (both in
the all-attempts-reprogram hybrid and in the accepted-only-reprogram hybrid, hence the
factor 2; the `qH + 1` accounts for the final verification query). The second term pays
for collisions among the signing oracle's own commitments. The third term glues the
per-attempt simulator across the restart loop, whose expected length is at most
`1/(1-p)` (see `tvDist_firstSome_le_geometric`); a simulator for the accepted-transcript
distribution itself (the paper's acHVZK notion) would shave this `1/(1-p)` factor. -/
noncomputable def cmaToNmaLoss (qS qH : ℕ) (ε p ζ_zk δ : ℝ) (_hp : p < 1) : ℝ :=
  2 * qS * (qH + 1) * ε / (1 - p) +
  qS * ε * (qS + 1) / (2 * (1 - p) ^ 2) +
  qS * ζ_zk / (1 - p) +
  δ

/-- The per-key part of `cmaToNmaLoss`: the statistical loss of the three signing-oracle
hybrid hops at a fixed good key pair. `cmaToNmaLoss` is this quantity plus the
key-regularity failure probability `δ`. -/
noncomputable def perKeyLoss (qS qH : ℕ) (ε p ζ_zk : ℝ) : ℝ :=
  2 * qS * (qH + 1) * ε / (1 - p) +
  qS * ε * (qS + 1) / (2 * (1 - p) ^ 2) +
  qS * ζ_zk / (1 - p)

lemma cmaToNmaLoss_eq_perKeyLoss_add (qS qH : ℕ) (ε p ζ_zk δ : ℝ) (hp : p < 1) :
    cmaToNmaLoss qS qH ε p ζ_zk δ hp = perKeyLoss qS qH ε p ζ_zk + δ := rfl

section scaffold

variable (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
variable (adv : SignatureAlg.unforgeableAdv
  (FiatShamirWithAbort
    (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts))

omit [SampleableType Stmt] in
/-- **Per-signing-query core of the Trans → Sim hop.** From any shared starting cache,
the accepted-only-reprogramming body and the simulated body are within total-variation
distance `ζ_zk · (1 + q + ⋯ + q^(maxAttempts-1)) ≤ ζ_zk / (1 - q)` on their joint
output-and-cache distribution, where `ζ_zk` bounds the per-attempt HVZK error and `q`
the simulator's per-attempt abort probability.

The cache programming is the same deterministic continuation on both sides
(`signProgramCont`), so the bound reduces to `tvDist_firstSome_le_geometric` on the
private restart loops. -/
lemma tvDist_run_transSignBody_simSignBody_le
    (pk : Stmt) (sk : Wit) (hrel : rel pk sk = true) (msg : M)
    {ζ_zk : ℝ} (hhvzk : ids.HVZK sim ζ_zk)
    {q : ℝ} (hq : Pr[= none | sim pk].toReal ≤ q) (hq0 : 0 ≤ q)
    (s : (M × Commit →ₒ Chal).QueryCache) :
    tvDist (StateT.run (transSignBody ids M maxAttempts pk sk msg) s)
        (StateT.run (simSignBody M maxAttempts sim pk sk msg) s) ≤
      ζ_zk * ∑ j ∈ Finset.range maxAttempts, q ^ j := by
  have hcore : tvDist (firstSome (ids.honestExecution pk sk) maxAttempts)
      (firstSome (sim pk) maxAttempts) ≤
        ζ_zk * ∑ j ∈ Finset.range maxAttempts, q ^ j :=
    tvDist_firstSome_le_geometric (ids.honestExecution pk sk) (sim pk)
      (hhvzk pk sk hrel) hq hq0 maxAttempts
  have hrw : ∀ (loop : ProbComp (Option (Commit × Chal × Resp))),
      StateT.run (liftM loop >>= signProgramCont M msg) s =
        loop >>= fun r => StateT.run (signProgramCont M msg r) s := by
    intro loop
    simp [StateT.run_bind]
  rw [transSignBody, simSignBody, hrw, hrw]
  exact le_trans (tvDist_bind_right_le _ _ _) hcore

/-- The hybrid unforgeability experiment at a fixed key pair: run the adversary with the
base handlers and the given signing body, then verify the forgery under the final cache
and apply the freshness check. Instantiating `signBody` with `realSignBody`,
`progSignBody`, `transSignBody`, and `simSignBody` yields the games G₀ — G₃ of the
CMA-to-NMA hybrid chain. -/
noncomputable def hybridExpAtKey
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp)))
    (pk : Stmt) : ProbComp Bool := do
  let ((msg, σ), (cache, signed)) ← StateT.run
    (simulateQ
      (hybridBaseImpl (Commit := Commit) (Chal := Chal) M + hybridSignImpl M signBody)
      (adv.main pk)) (∅, [])
  let ok ← StateT.run'
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
      ((FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk msg σ)) cache
  pure (decide (msg ∉ signed) && ok)

/-! ## Verification tail -/

/-- Verification-and-freshness continuation of `hybridExpAtKey`, as a function of the
adversary's forgery and the final hybrid state. -/
noncomputable def hybridVerifyCont (pk : Stmt)
    (z : (M × Option (Commit × Resp)) × ((M × Commit →ₒ Chal).QueryCache × List M)) :
    ProbComp Bool := do
  let ok ← StateT.run'
    (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
        (randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
      ((FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk z.1.1 z.1.2)) z.2.1
  pure (decide (z.1.1 ∉ z.2.2) && ok)

omit [SampleableType Stmt] in
lemma hybridExpAtKey_eq_run_bind
    (signBody : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp)))
    (pk : Stmt) :
    hybridExpAtKey ids hr M maxAttempts adv signBody pk =
      (simulateQ
          (hybridBaseImpl (Commit := Commit) (Chal := Chal) M + hybridSignImpl M signBody)
          (adv.main pk)).run (∅, []) >>=
        hybridVerifyCont ids hr M maxAttempts pk := by
  refine bind_congr fun z => ?_
  rcases z with ⟨⟨msg, σ⟩, cache, signed⟩
  rfl

omit [SampleableType Stmt] in
/-- The verification continuation only reads the cache at the forged message's points,
so it is insensitive to cache changes away from them. -/
lemma hybridVerifyCont_cache_congr (pk : Stmt) (ms : M × Option (Commit × Resp))
    (c₁ c₂ : (M × Commit →ₒ Chal).QueryCache) (l : List M)
    (h : ∀ w : Commit, c₁ (ms.1, w) = c₂ (ms.1, w)) :
    hybridVerifyCont ids hr M maxAttempts pk (ms, (c₁, l)) =
      hybridVerifyCont ids hr M maxAttempts pk (ms, (c₂, l)) := by
  rcases ms with ⟨msg, _ | ⟨w, zr⟩⟩
  · rfl
  · refine congrArg (· >>= fun ok => pure (decide (msg ∉ l) && ok)) ?_
    have hside : ∀ c : (M × Commit →ₒ Chal).QueryCache,
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          ((FiatShamirWithAbort
            (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
            ids hr M maxAttempts).verify pk msg (some (w, zr)))).run' c =
          (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            ids.verify pk w cu.1 zr) <$> roStep M c (msg, w) := by
      intro c
      simp only [FiatShamirWithAbort, simulateQ_bind, roSim.simulateQ_HasQuery_query,
        simulateQ_pure]
      change Prod.fst <$> (((randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) (msg, w) >>=
            fun cc => pure (ids.verify pk w cc zr)).run c) = _
      rw [StateT.run_bind]
      rw [show ((randomOracle : QueryImpl (M × Commit →ₒ Chal)
          (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) (msg, w)).run c =
        roStep M c (msg, w) from randomOracle_run_eq_roStep M c (msg, w)]
      simp
    rw [hside c₁, hside c₂]
    cases hc : c₁ (msg, w) with
    | some v =>
        rw [roStep_of_some M hc,
          roStep_of_some M (show c₂ (msg, w) = some v from (h w).symm.trans hc)]
        simp
    | none =>
        rw [roStep_of_none M hc,
          roStep_of_none M (show c₂ (msg, w) = none from (h w).symm.trans hc)]
        simp

omit [SampleableType Stmt] in
/-- When the forged message has already been signed, the freshness conjunct forces the
game output to `false`, so the success probability vanishes regardless of the cache. -/
lemma probOutput_true_hybridVerifyCont_of_mem (pk : Stmt)
    (ms : M × Option (Commit × Resp))
    (c : (M × Commit →ₒ Chal).QueryCache) (l : List M) (hmem : ms.1 ∈ l) :
    Pr[= true | hybridVerifyCont ids hr M maxAttempts pk (ms, (c, l))] = 0 := by
  rw [hybridVerifyCont, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_eq_zero.mpr fun ok => ?_
  rw [probOutput_pure, if_neg (by simp [hmem]), mul_zero]

/-! ## The lazy-side ghost-read charge -/

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- Transport a predicate-targeted query bound across a (propositionally equal) choice of
predicate and `DecidablePred` instance. The decidability instance is a subsingleton up to
the propositional content; this lets a query bound built with one instance feed a lemma
expecting another (e.g. the accumulator's synthesised instance). -/
lemma isQueryBoundP_cast_pred' {ι₀ : Type} {spec₀ : OracleSpec ι₀} {α₀ : Type}
    {oa : OracleComp spec₀ α₀} {p₁ p₂ : spec₀.Domain → Prop}
    {i₁ : DecidablePred p₁} {i₂ : DecidablePred p₂} {n : ℕ} (hp : p₁ = p₂)
    (h : @OracleComp.IsQueryBoundP _ spec₀ α₀ oa p₁ i₁ n) :
    @OracleComp.IsQueryBoundP _ spec₀ α₀ oa p₂ i₂ n := by
  subst hp
  rwa [Subsingleton.elim i₂ i₁]

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- **Bad-flag pass-through for a bad-free run.** If every output of `oa` carries bad bit
`false`, then the bad probability of `oa >>= k` is carried entirely by `oa`'s (good)
outputs: it equals the resource-weighted sum the accumulator's free/charged step premises
require, with no extra bad mass introduced by `oa` itself. -/
lemma probEvent_bad_bind_eq_tsum_false {γ' σ' δ' τ' : Type}
    (oa : ProbComp (γ' × σ' × Bool))
    (k : γ' × σ' × Bool → ProbComp (δ' × τ' × Bool))
    (hbf : ∀ z ∈ support oa, z.2.2 = false) :
    Pr[fun w => w.2.2 = true | oa >>= k]
      = ∑' z : γ' × σ',
          Pr[= (z.1, z.2, false) | oa] * Pr[fun w => w.2.2 = true | k (z.1, z.2, false)] := by
  classical
  rw [probEvent_bind_eq_tsum,
    ← (Equiv.prodAssoc γ' σ' Bool).tsum_eq
      (fun w => Pr[= w | oa] * Pr[fun y => y.2.2 = true | k w]),
    ENNReal.tsum_prod']
  refine tsum_congr fun z => ?_
  rw [tsum_bool]
  simp only [Equiv.prodAssoc_apply]
  have htrue : Pr[= (z.1, z.2, true) | oa] = 0 := by
    refine probOutput_eq_zero_of_not_mem_support fun hz => ?_
    exact absurd (hbf _ hz) (by simp)
  rw [htrue, zero_mul, add_zero]

omit [SampleableType Stmt] in
/-- **Charged-step premise for the lazy ghost read.** For the deferred-sampling handler
`lazyGhostHybridImpl`, an adversarial random-oracle read at `(.inl (.inr mc))` from a
non-bad state pays the amortizable flip charge `enncard (ghost cache) · ofReal ε` and
routes any residual bad mass through its `fired = false` (good) outputs. This is exactly
the `h_charged_step` hypothesis required by
`probEvent_bad_simulateQ_run_le_expectedQuerySlack`, made true (in contrast to the eager
handler's deterministic mass-`1` flip) by the lazy fire draw whose `true` mass is bounded
by `probOutput_lazyGhostFire_true_le_enncard`. -/
lemma probEvent_lazyGhostHybridImpl_charged_step (pk : Stmt) (sk : Wit) {ε : ℝ}
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (mc : M × Commit)
    (s : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M)
    (k : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
          (.inl (.inr mc))) ×
        (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) ×
          Bool →
        ProbComp ((M × Option (Commit × Resp)) ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) ×
            Bool)) :
    Pr[fun z => z.2.2 = true |
        ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inr mc))).run (s, false)) >>= k]
      ≤ QueryCache.enncard s.1.2 * ENNReal.ofReal ε +
        ∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (.inl (.inr mc))) ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
          Pr[= (z.1, z.2, false) |
            (lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inr mc))).run (s, false)] *
            Pr[fun w => w.2.2 = true | k (z.1, z.2, false)] := by
  classical
  obtain ⟨⟨re, gh⟩, list⟩ := s
  set fire := lazyGhostFire ids pk sk mc.2 gh.toSet.encard.toNat with hfire
  set ro := roStep M re mc with hro
  -- The lazy-fire `true`-mass is the amortizable flip charge `enncard gh · ofReal ε`.
  have h_fire_true : Pr[= true | fire] ≤ QueryCache.enncard gh * ENNReal.ofReal ε := by
    rw [hfire]
    refine (probOutput_lazyGhostFire_true_le ids pk sk hGuess mc.2 _).trans ?_
    gcongr
    -- `(encard.toNat : ℝ≥0∞) ≤ (encard : ℝ≥0∞) = enncard gh`.
    change ((gh.toSet.encard.toNat : ℕ) : ℝ≥0∞) ≤ (gh.toSet.encard : ℝ≥0∞)
    calc ((gh.toSet.encard.toNat : ℕ) : ℝ≥0∞)
        = ((gh.toSet.encard.toNat : ℕ∞) : ℝ≥0∞) := by push_cast; rfl
      _ ≤ (gh.toSet.encard : ℝ≥0∞) := ENat.toENNReal_mono (ENat.coe_toNat_le_self _)
  -- The run, with its bad bit reduced (`false || b = b`): a fire draw whose Boolean result
  -- becomes the output bad bit, composed with the real-layer caching read `ro`.
  have h_run : (lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inr mc))).run
        (((re, gh), list), false) =
      fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro := by
    simp only [hfire, hro]
    rfl
  -- Rewrite both the run-bind and the good-continuation sum into the reduced form, then
  -- expand the bad probability over each run output (`Chal × σ × Bool`).
  rw [h_run, probEvent_bind_eq_tsum]
  -- Unfold the `GhostState` abbreviation so the product structure is explicit.
  simp only [GhostState] at *
  -- Split each output sum over its Boolean (bad) coordinate.
  rw [← (Equiv.prodAssoc
      (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
        (Sum.inl (Sum.inr mc)))
      (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M)
      Bool).tsum_eq,
    ENNReal.tsum_prod']
  -- The `bad = false` summand is the accumulator's good-continuation term; the `bad = true`
  -- summand sums to the run's bad-output mass, bounded by `enncard gh · ofReal ε`.
  have h_split : ∀ z : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) ×
        (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
      (∑' b : Bool,
        Pr[= (z.1, z.2, b) |
          fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
          Pr[fun y => y.2.2 = true | k (z.1, z.2, b)])
      = Pr[= (z.1, z.2, false) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
          Pr[fun y => y.2.2 = true | k (z.1, z.2, false)]
        + Pr[= (z.1, z.2, true) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
          Pr[fun y => y.2.2 = true | k (z.1, z.2, true)] := by
    intro z
    rw [tsum_bool, add_comm]
  simp only [Equiv.prodAssoc_apply]
  -- Split each per-output Boolean sum into its `false` (good continuation) and `true`
  -- (bad output) parts, then separate the two sums.
  have hsplit_sum :
      (∑' a : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
        ∑' b : Bool,
          Pr[= (a.1, a.2, b) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
            Pr[fun z => z.2.2 = true | k (a.1, a.2, b)])
      = (∑' a : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) ×
            (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
          Pr[= (a.1, a.2, false) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
            Pr[fun z => z.2.2 = true | k (a.1, a.2, false)])
        + (∑' a : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inr mc))) ×
            (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
          Pr[= (a.1, a.2, true) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
            Pr[fun z => z.2.2 = true | k (a.1, a.2, true)]) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun a => h_split a
  refine le_trans (le_of_eq hsplit_sum) ?_
  rw [add_comm]
  refine add_le_add ?_ le_rfl
  -- The bad-output (`b = true`) mass is at most the fire `true`-mass: each output's bad bit
  -- is the fire result, and the continuation contributes at most `1`.
  calc (∑' z : Chal ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
        Pr[= (z.1, z.2, true) |
          fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] *
          Pr[fun y => y.2.2 = true | k (z.1, z.2, true)])
      ≤ ∑' z : Chal ×
          (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
          Pr[= (z.1, z.2, true) |
            fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        exact mul_le_of_le_one_right (zero_le') probEvent_le_one
    _ ≤ Pr[= true | fire] := by
        -- Each output's bad bit equals the fire draw, so the `b = true` outputs carry
        -- at most the fire `true`-mass. Expand each summand over the fire draw, swap the
        -- sums, and use that `g_fired <$> ro` outputs bad bit `fired`.
        have h_per_z : ∀ z : Chal ×
            (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
            Pr[= (z.1, z.2, true) |
              fire >>= fun fired => (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro]
            = ∑' fired : Bool, Pr[= fired | fire] *
                Pr[= (z.1, z.2, true) |
                  (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro] :=
          fun z => probOutput_bind_eq_tsum fire _ _
        rw [tsum_congr h_per_z, ENNReal.tsum_comm]
        -- The inner sum over outputs is `0` for `fired = false` (its outputs carry bad bit
        -- `false`) and `≤ 1` for `fired = true`, giving the bound `≤ Pr[= true | fire]`.
        have h_inner : ∀ fired : Bool,
            (∑' z : Chal ×
              (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
              Pr[= fired | fire] *
                Pr[= (z.1, z.2, true) |
                  (fun cu => (cu.1, (((cu.2, gh), list), fired))) <$> ro])
              ≤ Pr[= fired | fire] * (if fired then 1 else 0) := by
          intro fired
          rw [ENNReal.tsum_mul_left]
          gcongr ?_ * ?_
          cases fired with
          | false =>
              rw [if_neg (by decide)]
              refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun z => ?_)
              refine probOutput_eq_zero_of_not_mem_support ?_
              rw [support_map]
              rintro ⟨cu, _, heq⟩
              simp only [Prod.mk.injEq] at heq
              exact absurd heq.2.2 (by decide)
          | true =>
              rw [if_pos rfl]
              -- The bad-output mass is a sub-sum of the total mass `≤ 1`, via the injection
              -- `z ↦ (z.1, z.2, true)`.
              refine le_trans (ENNReal.tsum_comp_le_tsum_of_injective ?_
                (fun w => Pr[= w | (fun cu => (cu.1, (((cu.2, gh), list), true))) <$> ro]))
                tsum_probOutput_le_one
              rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
              simp only [Prod.mk.injEq] at heq
              exact Prod.ext heq.1 heq.2.1
        refine le_trans (ENNReal.tsum_le_tsum h_inner) ?_
        rw [tsum_bool]
        simp
    _ ≤ QueryCache.enncard gh * ENNReal.ofReal ε := h_fire_true

omit [SampleableType Stmt] in
/-- A uniform-sampling read of the lazy ghost handler preserves the bad flag: started from a
non-bad state, every output is non-bad. -/
lemma lazyGhostHybridImpl_run_unif_bad_false (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : GhostState M Commit Chal) (hs : s.2 = false) :
    ∀ z ∈ support ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inl n))).run s),
      z.2.2 = false := by
  intro z hz
  rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n from rfl]
    at hz
  obtain ⟨u, _, heq⟩ :=
    (support_map (fun u => (u, s)) ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n)
      ▸ hz)
  rw [← heq, hs]

omit [SampleableType Stmt] in
/-- A signing query of the lazy ghost handler preserves the bad flag: started from a non-bad
state, every output is non-bad. -/
lemma lazyGhostHybridImpl_run_sign_bad_false (pk : Stmt) (sk : Wit) (msg : M)
    (s : GhostState M Commit Chal) (hs : s.2 = false) :
    ∀ z ∈ support ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inr msg)).run s),
      z.2.2 = false := by
  intro z hz
  rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (.inr msg)).run s =
      (fun alc => (alc.1, ((alc.2, msg :: s.1.2), s.2))) <$>
        (ghostSignBody ids M pk sk msg maxAttempts).run s.1.1 from rfl] at hz
  obtain ⟨alc, _, heq⟩ :=
    (support_map (fun alc : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
        (alc.1, ((alc.2, msg :: s.1.2), s.2)))
      ((ghostSignBody ids M pk sk msg maxAttempts).run s.1.1) ▸ hz)
  rw [← heq, hs]

omit [SampleableType Stmt] in
/-- **Deliverable A: the lazy-side ghost-read bound.** For the deferred-sampling handler
`lazyGhostHybridImpl`, the probability that the adversary's run ever flips the bad flag is
at most `qS·(qH+1)·ε/(1-p)`.

Assembled from the single-world resource-charged accumulator
`probEvent_bad_simulateQ_run_le_expectedQuerySlack` (charged step =
`probEvent_lazyGhostHybridImpl_charged_step`, free step = the bad-flag pass-through of
non-read queries) chained with the charged-read / expected-growth fold
`expectedQuerySlack_charged_read_expected_growth_le` (resource `R s := enncard (ghost
cache)`, per-read charge `ofReal ε`, expected growth `g := ∑_{a<maxAttempts} ofReal p^a` per
signing query via `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le`), with the
charged-read budget `qH+1` and the growth-query budget `qS` from `hQ`, the empty starting
ghost cache contributing `R = 0`, and `g ≤ 1/(1-p)`. -/
lemma probEvent_lazyGhostHybridImpl_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (lazyGhostHybridImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
  classical
  -- ASSEMBLY RECIPE (all ingredients PROVEN; blocked only by elaboration performance).
  --
  -- (1) Single-world accumulator
  --     `OracleComp.ProgramLogic.Relational.probEvent_bad_simulateQ_run_le_expectedQuerySlack`
  --     at `impl := lazyGhostHybridImpl ids M maxAttempts pk sk`,
  --     `charged := (· matches Sum.inl (Sum.inr _))` (random-oracle reads),
  --     `R s := QueryCache.enncard s.1.2` (the ghost cache size), `ε := ofReal ε`, with
  --       * `h_charged_step := probEvent_lazyGhostHybridImpl_charged_step …` (PROVEN above);
  --       * `h_free_step` from the bad-flag pass-through `probEvent_bad_bind_eq_tsum_false`
  --         combined with `lazyGhostHybridImpl_run_unif_bad_false` /
  --         `lazyGhostHybridImpl_run_sign_bad_false` (all PROVEN above);
  --       * charged-read budget `qH + 1` from `(hQ pk).2.mono` transported across the
  --         `DecidablePred` instance by `isQueryBoundP_cast_pred'` (PROVEN above).
  --     This yields
  --       `Pr[bad | run] ≤ expectedQuerySlack lazyGhostHybridImpl charged
  --                          (fun s => R s * ofReal ε) (adv.main pk) (qH+1) (init, false)`.
  --
  -- (2) The charged-read / expected-growth fold
  --     `OracleComp.ProgramLogic.Relational.expectedQuerySlack_charged_read_expected_growth_le`
  --     with `chargedQuery := reads`, `growthQuery := (· matches Sum.inr _)` (signings),
  --     `R`, `β := ofReal ε`, `g := ∑_{a<maxAttempts} ofReal p_abort ^ a`, where
  --       * `h_charged` / `h_free`: a read / uniform query leaves the ghost cache `R`
  --         unchanged (output ghost cache `= s.1.2`), so `R z.2.1 ≤ R p.1` (in fact `=`);
  --       * `h_growth`: the ghost-layer growth law
  --         `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le ids … hAbort` gives
  --         `∑ Pr[=z|signing.run]·enncard z.2.2 ≤ enncard gh + ∑_{a} ofReal p^a = R p.1 + g`;
  --       * growth budget `qS` from `(hQ pk).1`.
  --     This yields `expectedQuerySlack … (qH+1) (init,false) ≤ (qH+1)·(R init + qS·g)·ofReal ε`.
  --
  -- (3) Arithmetic: `R init = enncard ∅ = 0`, and `g = ∑_{a<maxAttempts} ofReal p^a ≤
  --     1/(1-p_abort)` (geometric bound `geom_sum_mul`, cf. `hSgeo` in
  --     `probEvent_charge_signCollision_le`), giving
  --       `(qH+1)·(0 + qS·g)·ofReal ε ≤ ofReal (qS·(qH+1)·ε/(1-p_abort))`
  --     via `ENNReal.ofReal` push-through (cf. the closing block of
  --     `probEvent_charge_signCollision_le`).
  --
  refine (OracleComp.ProgramLogic.Relational.probEvent_bad_simulateQ_run_le_expectedQuerySlack
    (impl := lazyGhostHybridImpl ids M maxAttempts pk sk)
    (charged := fun t => t matches Sum.inl (Sum.inr _))
    (R := fun s => QueryCache.enncard s.1.2) (ε := ENNReal.ofReal ε)
    ?_ ?_ (adv.main pk) (qS := qH + 1) ?_ (((∅, ∅), []))).trans ?_
  · -- h_charged_step: a charged random-oracle read pays `enncard · ofReal ε`.
    rintro t s ht k
    obtain ⟨mc, rfl⟩ : ∃ mc, t = Sum.inl (Sum.inr mc) := by
      revert ht; rcases t with (n | mc) | msg <;> simp
    exact probEvent_lazyGhostHybridImpl_charged_step ids M maxAttempts pk sk hGuess mc s k
  · -- h_free_step: a non-charged (uniform or signing) query introduces no bad mass.
    rintro t s ht k
    rcases t with (n | mc) | msg
    · exact le_of_eq (probEvent_bad_bind_eq_tsum_false
        (oa := (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run (s, false))
        (k := k)
        (lazyGhostHybridImpl_run_unif_bad_false ids M maxAttempts pk sk n (s, false) rfl))
    · exact absurd rfl ht
    · exact le_of_eq (probEvent_bad_bind_eq_tsum_false
        (oa := (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inr msg)).run (s, false))
        (k := k)
        (lazyGhostHybridImpl_run_sign_bad_false ids M maxAttempts pk sk msg (s, false) rfl))
  · -- charged-read budget `qH + 1`: from the RO-read bound `qH`, weakened by `+1`.
    have h := (hQ pk).2.mono (Nat.le_succ qH)
    convert h using 3 with x
    rcases x with (_ | _) | _ <;> rfl
  · -- (2)+(3): the charged-read / expected-growth fold, then arithmetic.
    set g : ℝ≥0∞ := ∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a with hg
    -- The fold bound: `expectedQuerySlack ≤ (qH+1)·(R init + qS·g)·ofReal ε`.
    have h_fold :
        OracleComp.ProgramLogic.Relational.expectedQuerySlack
            (lazyGhostHybridImpl ids M maxAttempts pk sk)
            (fun t => t matches Sum.inl (Sum.inr _))
            (fun s => QueryCache.enncard s.1.2 * ENNReal.ofReal ε) (adv.main pk) (qH + 1)
            ((((∅, ∅), []) :
              ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M),
                false)
          ≤ ((qH + 1 : ℕ) : ℝ≥0∞) *
              (QueryCache.enncard (∅ : (M × Commit →ₒ Chal).QueryCache) + (qS : ℝ≥0∞) * g) *
              ENNReal.ofReal ε := by
      refine OracleComp.ProgramLogic.Relational.expectedQuerySlack_charged_read_expected_growth_le
        (lazyGhostHybridImpl ids M maxAttempts pk sk)
        (chargedQuery := fun t => t matches Sum.inl (Sum.inr _))
        (growthQuery := fun t => t matches Sum.inr _)
        (R := fun s => QueryCache.enncard s.1.2) (β := ENNReal.ofReal ε) (g := g)
        ?_ ?_ ?_ (adv.main pk) ?_ ?_ _
      · -- h_charged: a charged RO read leaves the ghost cache (`R`) unchanged.
        rintro t p hp ht z hz
        rcases t with (n | mc) | msg
        · exact absurd ht (by simp)
        · rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run p =
              lazyGhostFire ids pk sk mc.2 p.1.1.2.toSet.encard.toNat >>= fun fired =>
                (fun cu => (cu.1, (((cu.2, p.1.1.2), p.1.2), p.2 || fired))) <$>
                  roStep M p.1.1.1 mc from rfl] at hz
          obtain ⟨fired, _, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
          obtain ⟨cu, _, heq⟩ :=
            (support_map (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
                (cu.1, (((cu.2, p.1.1.2), p.1.2), p.2 || fired)))
              (roStep M p.1.1.1 mc) ▸ hz)
          rw [← heq]
        · exact absurd ht (by simp)
      · -- h_growth: the ghost-layer growth law for a signing query.
        rintro t p hp ht ht2
        rcases t with (n | mc) | msg
        · exact absurd ht2 (by simp)
        · exact absurd ht2 (by simp)
        · obtain ⟨⟨⟨re, gh⟩, list⟩, b⟩ := p
          rw [show b = false from hp]
          change ∑' z : (Option (Commit × Resp)) ×
              (((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) × Bool,
              Pr[= z | (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inr msg)).run
                (((re, gh), list), false)] * QueryCache.enncard z.2.1.1.2
            ≤ QueryCache.enncard gh + g
          rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inr msg)).run
                (((re, gh), list), false) =
              (ghostSignBody ids M pk sk msg maxAttempts).run (re, gh) >>= fun alc =>
                pure (alc.1, ((alc.2, msg :: list), false)) from rfl]
          have heq := tsum_probOutput_bind_mul
            ((ghostSignBody ids M pk sk msg maxAttempts).run (re, gh))
            (fun alc => (pure (alc.1, ((alc.2, msg :: list), false)) : ProbComp _))
            (fun z => QueryCache.enncard z.2.1.1.2)
          refine le_trans (le_of_eq heq) ?_
          refine le_trans (ENNReal.tsum_le_tsum fun alc => ?_)
            (tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le ids M pk sk msg hAbort
              maxAttempts re gh)
          rw [tsum_probOutput_pure_mul]
      · -- h_free: a uniform query leaves the ghost cache (`R`) unchanged.
        rintro t p hp ht ht2 z hz
        rcases t with (n | mc) | msg
        · rw [show (lazyGhostHybridImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run p =
              (fun u => (u, p)) <$>
                (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n from rfl] at hz
          obtain ⟨u, _, heq⟩ :=
            (support_map (fun u => (u, p))
              ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) ▸ hz)
          rw [← heq]
        · exact absurd ht (by simp)
        · exact absurd ht2 (by simp)
      · -- charged budget `qH + 1`.
        have h := (hQ pk).2.mono (Nat.le_succ qH)
        convert h using 3 with x
        rcases x with (_ | _) | _ <;> rfl
      · -- growth budget `qS`.
        have h := (hQ pk).1
        convert h using 3 with x
        rcases x with (_ | _) | _ <;> rfl
    refine h_fold.trans ?_
    -- (3) Arithmetic: `enncard ∅ = 0`, `g = ofReal S` with `S = ∑ pᵃ ≤ 1/(1-p)`.
    have h1p : (0 : ℝ) < 1 - p_abort := by linarith
    set S : ℝ := ∑ a ∈ Finset.range maxAttempts, p_abort ^ a with hSdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun a _ => pow_nonneg hp₀ a
    have hg_eq : g = ENNReal.ofReal S := by
      rw [hg, hSdef, ENNReal.ofReal_sum_of_nonneg (fun a _ => pow_nonneg hp₀ a)]
      exact Finset.sum_congr rfl fun a _ => by rw [← ENNReal.ofReal_pow hp₀]
    have hSgeo : S ≤ 1 / (1 - p_abort) := by
      rw [hSdef, le_div_iff₀ h1p]
      have hmul := geom_sum_mul p_abort maxAttempts
      nlinarith [pow_nonneg hp₀ maxAttempts]
    rw [QueryCache.enncard_empty, zero_add, hg_eq,
      show ((qH + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((qH : ℝ) + 1) from by
        rw [← ENNReal.ofReal_natCast (qH + 1)]; push_cast; ring_nf,
      show (qS : ℝ≥0∞) = ENNReal.ofReal qS from (ENNReal.ofReal_natCast qS).symm]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hqS : (0 : ℝ) ≤ qS := Nat.cast_nonneg qS
    have hqH1 : (0 : ℝ) ≤ (qH : ℝ) + 1 := by positivity
    calc ((qH : ℝ) + 1) * (qS * S) * ε
        ≤ ((qH : ℝ) + 1) * (qS * (1 / (1 - p_abort))) * ε := by
          gcongr
      _ = qS * ((qH : ℝ) + 1) * ε / (1 - p_abort) := by ring

/-! ## Direct route: averaged multi-key hidden-read fold to the target

The direct route bounds the eager ghost-read bad probability by the banked multi-key
hidden-target first-fire bound `OracleComp.probEvent_hiddenReadList_le` (`≤ n·(qH+1)·ε`
for `n` ghost keys), then averages the per-key-count bound over the run's key-count law.
The averaging step is the pure-`ℝ≥0∞` arithmetic fold `hiddenReadList_fold_le_target`
below: it takes any sub-probability weight `P : ℕ → ℝ≥0∞` over the number of ghost keys
whose mean is bounded by the expected attempt count `qS/(1-p)` (the banked
`tsum_probOutput_commit_mul_abort_le` aggregate) and folds the per-count bound
`k·(qH+1)·ε` into the target `qS·(qH+1)·ε/(1-p)`. It is the closed `[fold]` step of the
direct chain `Pr[eager bad] ≤[D1] Pr[readManyList …] =[D2] Pr[hiddenReadList …] ≤ n·(qH+1)·ε
≤[fold] target`; the remaining `[D1]`/`[D2]` connection is the deferred-sampling
commutation isolated in `eagerGhostRead_bad_le_lazyGhostRead_bad`. -/
lemma hiddenReadList_fold_le_target (qS qH : ℕ) (ε p_abort : ℝ) (hp : p_abort < 1)
    (P : ℕ → ℝ≥0∞)
    (hmean : ∑' k : ℕ, P k * (k : ℝ≥0∞) ≤ ENNReal.ofReal (qS / (1 - p_abort))) :
    (∑' k : ℕ, P k * ((k : ℝ≥0∞) * (((qH : ℝ≥0∞) + 1) * ENNReal.ofReal ε)))
      ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  have hqH1 : ((qH : ℝ≥0∞) + 1) = ENNReal.ofReal ((qH : ℝ) + 1) := by
    rw [← ENNReal.ofReal_natCast qH, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by positivity) (by norm_num)]
  have h1 : (∑' k : ℕ, P k * ((k : ℝ≥0∞) * (((qH : ℝ≥0∞) + 1) * ENNReal.ofReal ε)))
      = (∑' k : ℕ, P k * (k : ℝ≥0∞)) * (ENNReal.ofReal ((qH : ℝ) + 1) * ENNReal.ofReal ε) := by
    rw [← ENNReal.tsum_mul_right]; congr 1; ext k; rw [hqH1]; ring
  rw [h1, ← ENNReal.ofReal_mul (by positivity)]
  calc (∑' k : ℕ, P k * (k : ℝ≥0∞)) * ENNReal.ofReal (((qH : ℝ) + 1) * ε)
      ≤ ENNReal.ofReal (qS / (1 - p_abort)) * ENNReal.ofReal (((qH : ℝ) + 1) * ε) := by gcongr
    _ = ENNReal.ofReal (qS / (1 - p_abort) * (((qH : ℝ) + 1) * ε)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
        apply ENNReal.ofReal_le_ofReal; apply le_of_eq; field_simp

omit [SampleableType Stmt] in
/-- **(c) Expected-attempt geometric fold.** The per-signing-query attempt-count mass
`∑_{a<maxAttempts} ofReal p^a` — which counts *all* attempts (each attempt `a` is reached
with probability `≤ pᵃ`, *including* the accepting one) — is bounded by `ofReal (1/(1-p))`.
This is the geometric sum that turns the per-query charge increment of
`tsum_probOutput_run_ghostSignBody_mul_memCharge_le` (factor `∑_{a<maxAttempts} pᵃ`) into the
`1/(1-p)` factor of the target `qS·(qH+1)·ε/(1-p)`. -/
lemma geomAttemptSum_le {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) :
    (∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a)
      ≤ ENNReal.ofReal (1 / (1 - p_abort)) := by
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set S : ℝ := ∑ a ∈ Finset.range maxAttempts, p_abort ^ a with hSdef
  have hg_eq : (∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a)
      = ENNReal.ofReal S := by
    rw [hSdef, ENNReal.ofReal_sum_of_nonneg (fun a _ => pow_nonneg hp₀ a)]
    exact Finset.sum_congr rfl fun a _ => by rw [← ENNReal.ofReal_pow hp₀]
  rw [hg_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hSdef, le_div_iff₀ h1p]
  have hmul := geom_sum_mul p_abort maxAttempts
  nlinarith [pow_nonneg hp₀ maxAttempts]

omit [SampleableType Stmt] in
/-- **General geometric attempt-count fold.** For any number of terms `n`, the geometric sum
`∑_{a<n} ofReal p^a` is bounded by `ofReal (1/(1-p))`. The general-`n` companion of
`geomAttemptSum_le` (which fixes `n = maxAttempts`); needed at `n = maxAttempts + 1` for the
attempt-count charge `∑_{a≤maxAttempts} p^a = (reject sum) + 1`. -/
lemma geomSum_le {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (n : ℕ) :
    (∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a)
      ≤ ENNReal.ofReal (1 / (1 - p_abort)) := by
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  have hg_eq : (∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a)
      = ENNReal.ofReal (∑ a ∈ Finset.range n, p_abort ^ a) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => pow_nonneg hp₀ a)]
    exact Finset.sum_congr rfl fun a _ => by rw [← ENNReal.ofReal_pow hp₀]
  rw [hg_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ h1p]
  have hmul := geom_sum_mul p_abort n
  nlinarith [pow_nonneg hp₀ n]

/-! ## Deferred-sampling eager↔lazy coupling (ghost-read leaf) -/

omit [SampleableType Stmt] in
/-- **Uniform-branch per-query coupling for the eager↔lazy ghost handlers** (banked). On a
uniform query both `ghostHybridImpl … true` and `lazyGhostHybridImpl` forward the draw and
leave the state untouched (`lazyGhostHybridImpl_run_unif_eq`), so they are coupled by the
identity coupling on the shared uniform sample with *equal outputs* and the bad-flag
implication preserved verbatim. This is the divergence-free branch of `h_step`. -/
theorem relTriple_ghostHybrid_lazyGhost_unif (pk : Stmt) (sk : Wit)
    (n : unifSpec.Domain) (e l : GhostState M Commit Chal) (hRel : e.2 = true → l.2 = true) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inl n))).run e)
      ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inl (.inl n))).run l)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ (p₁.2.2 = true → p₂.2.2 = true)) := by
  classical
  rw [lazyGhostHybridImpl_run_unif_eq ids M maxAttempts pk sk n l]
  simp only [ghostHybridImpl, StateT.run_mk]
  refine OracleComp.ProgramLogic.Relational.relTriple_bind
    (OracleComp.ProgramLogic.Relational.relTriple_refl
      ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n)) ?_
  rintro u u' rfl
  exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, hRel⟩

omit [SampleableType Stmt] in
/-- **Signing-branch per-query coupling for the eager↔lazy ghost handlers** (banked). On a
signing query both handlers run the *same* `ghostSignBody` over the layered cache, prepend
`msg` to the signed-message list, and leave the bad flag untouched
(`lazyGhostHybridImpl_run_sign_eq`); they are therefore identical, so coupled by the
identity coupling with equal outputs and the bad-flag implication preserved. This is the
second divergence-free branch of `h_step`. -/
theorem relTriple_ghostHybrid_lazyGhost_sign (pk : Stmt) (sk : Wit)
    (msg : M) (e l : GhostState M Commit Chal) (hRel : e.2 = true → l.2 = true) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run e)
      ((lazyGhostHybridImpl ids M maxAttempts pk sk (.inr msg)).run l)
      (fun p₁ p₂ => p₁.2.2 = true → p₂.2.2 = true) := by
  classical
  -- The signing handlers copy the input bad flag to the output (`alc ↦ (…, s.2)`), so the
  -- output bad flag is the *constant* `e.2` on the left and `l.2` on the right, independent of
  -- the `ghostSignBody` draw. Couple the two (possibly differently-cached) `ghostSignBody`
  -- runs by *any* coupling (the product coupling from `relTriple_true`), then map both to
  -- `pure`s whose bad flags are `e.2` / `l.2`; the post is then exactly `hRel`.
  rw [lazyGhostHybridImpl_run_sign_eq ids M maxAttempts pk sk msg l]
  simp only [ghostHybridImpl, StateT.run_mk]
  refine OracleComp.ProgramLogic.Relational.relTriple_bind
    (OracleComp.ProgramLogic.Relational.relTriple_true
      ((ghostSignBody ids M pk sk msg maxAttempts).run e.1.1)
      ((ghostSignBody ids M pk sk msg maxAttempts).run l.1.1)) ?_
  rintro a b -
  exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure hRel

/-! ## Measure-level eager↔lazy coupling: support lemmas

The lemmas in this section supply bookkeeping used by `avgBadM_eager_le_lazy_joint`
(banked below as a reusable two-measure coupling engine). Both handlers agree on uniform
and signing steps (banked as `relTriple_ghostHybrid_lazyGhost_unif` /
`relTriple_ghostHybrid_lazyGhost_sign`), so the per-step premises concern the per-step
invariant-preservation at those steps: expected ghost-cache size, flag-preservation,
charge-carry, and charge-K bookkeeping. For the uniform and signing branches both handlers
are definitionally identical (`lazyGhostHybridImpl_run_unif_eq` /
`lazyGhostHybridImpl_run_sign_eq`), so the post-step measures agree and any coupling
invariant is threaded unchanged. -/

open scoped Classical in
/-- **Uniform-handler pushforward identity (inert plumbing).** The uniform branch of
`ghostHybridImpl` is the state-fixing pushforward `(fun u => (u, p)) <$> oa` of the uniform
draw `oa`. Averaging a functional `F` over the post-step `(output, state)` pair therefore
collapses the state coordinate to the fixed `p`: the per-`p` inner sum equals the plain
uniform average of `F (·, p)`. Pure measure-theoretic rearrangement (`ENNReal.tsum_prod'`,
off-diagonal collapse, `probOutput_map_injective` on the injective `(·, p)`); no
probabilistic content. -/
lemma tsum_probOutput_map_state_fixed {R G : Type} (oa : ProbComp R) (p : G)
    (F : R × G → ℝ≥0∞) :
    (∑' z : R × G, Pr[= z | (fun u => (u, p)) <$> oa] * F z)
      = ∑' u : R, Pr[= u | oa] * F (u, p) := by
  classical
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun u => ?_
  rw [tsum_eq_single p ?_]
  · rw [probOutput_map_injective oa (f := fun u => (u, p))
      (fun a b h => (Prod.ext_iff.mp h).1) u]
  · intro g hg
    rw [probOutput_eq_zero_of_not_mem_support, zero_mul]
    intro hmem
    rw [support_map] at hmem
    obtain ⟨u', _, hu'⟩ := hmem
    exact hg (Prod.ext_iff.mp hu').2.symm

omit [SampleableType Stmt] in
/-- Uniform step preserves the per-state expected ghost size: the handler returns `(u, p)`
fixing the state, so the post-step ghost layer is always `p`'s. -/
lemma ghostHybridImpl_unif_expected_enncard (pk : Stmt) (sk : Wit)
    (n : unifSpec.Domain) (p : GhostState M Commit Chal) :
    (∑' z : unifSpec.Range n × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inl n))).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = QueryCache.enncard (p.1.1.2) := by
  classical
  calc (∑' z : unifSpec.Range n × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inl n))).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = ∑' u : unifSpec.Range n,
          Pr[= u | (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n] *
            QueryCache.enncard (p.1.1.2) :=
        tsum_probOutput_map_state_fixed
          ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) p
          (fun z => QueryCache.enncard (z.2.1.1.2))
    _ = QueryCache.enncard (p.1.1.2) := by
        rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

omit [SampleableType Stmt] in
/-- Read step preserves the per-state expected ghost size: the eager read writes only the
*base* cache layer (or flips the bad flag), never the ghost layer. -/
lemma ghostHybridImpl_read_expected_enncard (pk : Stmt) (sk : Wit)
    (mc : M × Commit) (p : GhostState M Commit Chal) :
    (∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = QueryCache.enncard (p.1.1.2) := by
  classical
  have hghost : ∀ z : Chal × GhostState M Commit Chal,
      z ∈ support ((ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p) →
      z.2.1.1.2 = p.1.1.2 := by
    intro z hz
    simp only [ghostHybridImpl, StateT.run_mk] at hz
    rcases hgh : p.1.1.2 mc with _ | v
    · simp only [hgh, support_map] at hz
      obtain ⟨cu, _, rfl⟩ := hz; rfl
    · simp only [hgh, ↓reduceIte, support_pure] at hz
      subst hz; rfl
  have hconst : (∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = ∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          QueryCache.enncard (p.1.1.2) := by
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support ((ghostHybridImpl ids M maxAttempts true pk sk
        (.inl (.inr mc))).run p)
    · congr 1
      exact congrArg QueryCache.enncard (hghost z hz)
    · have h0 : Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p]
          = 0 := probOutput_eq_zero_of_not_mem_support hz
      rw [h0, zero_mul, zero_mul]
  rw [hconst, ENNReal.tsum_mul_right]
  have hone : (∑' z : Chal × GhostState M Commit Chal,
      Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p]) = 1 := by
    refine tsum_probOutput_eq_one' ?_
    simp only [ghostHybridImpl, StateT.run_mk]
    rcases hgh : p.1.1.2 mc with _ | v
    · rcases p.1.1.1 mc with _ | v' <;> simp [roStep]
    · simp
  rw [hone, one_mul]

omit [SampleableType Stmt] in
/-- Sign step grows the per-state expected ghost size by at most `∑ attempts ≤ 1/(1-p)`: the
signing body's accepted-transcript / rejected-attempt programming writes to the ghost layer
(banked `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le` plus the geometric fold). -/
lemma ghostHybridImpl_sign_expected_enncard_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (p : GhostState M Commit Chal) :
    (∑' z : Option (Commit × Resp) × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run p] *
          QueryCache.enncard (z.2.1.1.2))
      ≤ QueryCache.enncard (p.1.1.2) + ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  -- The handler maps the `ghostSignBody` output state into the ghost layer; the expected
  -- ghost size of the result equals that of the `ghostSignBody` output's ghost component.
  have hmap : (∑' z : Option (Commit × Resp) × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run p] *
          QueryCache.enncard (z.2.1.1.2))
      = ∑' w : Option (Commit × Resp) ×
          ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache),
        Pr[= w | (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1] *
          QueryCache.enncard (w.2.2) := by
    rw [show (ghostHybridImpl ids M maxAttempts true pk sk (.inr msg)).run p
          = (fun alc => (alc.1, ((alc.2, msg :: p.1.2), p.2))) <$>
            (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1 from rfl]
    -- Reindex the post-step sum over the injective map `alc ↦ (alc.1, ((alc.2, …), …))`.
    set g : Option (Commit × Resp) ×
        ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) →
        Option (Commit × Resp) × GhostState M Commit Chal :=
      fun alc => (alc.1, ((alc.2, msg :: p.1.2), p.2)) with hg
    have hginj : Function.Injective g := by
      intro a b hab
      simp only [hg, Prod.mk.injEq] at hab
      exact Prod.ext hab.1 hab.2.1.1
    refine tsum_eq_tsum_of_ne_zero_bij (fun w => g w.1) ?_ ?_ ?_
    · intro a b hab
      exact Subtype.ext (hginj hab)
    · intro z hz
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hz
      have hzs : z ∈ support (g <$> (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1) :=
        (mem_support_iff _ z).mpr hz.1
      rw [support_map] at hzs
      obtain ⟨w, hw, rfl⟩ := hzs
      refine ⟨⟨w, ?_⟩, rfl⟩
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
      refine ⟨probOutput_ne_zero_of_mem_support hw, ?_⟩
      have heq : ((g w).2.1.1.2) = w.2.2 := rfl
      rw [heq] at hz; exact hz.2
    · rintro ⟨w, hw⟩
      change Pr[= g w | g <$> (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1] *
          QueryCache.enncard ((g w).2.1.1.2)
        = Pr[= w | (ghostSignBody ids M pk sk msg maxAttempts).run p.1.1] *
          QueryCache.enncard (w.2.2)
      rw [probOutput_map_injective _ hginj]
  rw [hmap]
  refine le_trans (tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le ids M pk sk msg
    hAbort maxAttempts p.1.1.1 p.1.1.2) ?_
  gcongr
  exact geomAttemptSum_le maxAttempts hp₀ hp

/-- **Per-state ghost charge accumulator** for the threaded eager-charge bound: the
mass-weighted total size of the ghost cache layer. Linear in the state measure `ν`, preserved
by read/uniform steps (which never write the ghost layer) and grown additively by sign steps
(banked `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le`). -/
noncomputable def ghostChargeK (ν : GhostState M Commit Chal → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' p : GhostState M Commit Chal, ν p * QueryCache.enncard (p.1.1.2)

/-- **Averaged ghost-membership charge invariant.** For every read target `mc`, the
`ν`-averaged membership charge at `mc` is dominated by the ghost-size accumulator scaled by
`ofReal ε`. This is the carried invariant of the threaded eager-charge bound: it holds at the
empty-cache Dirac start (`0 ≤ 0`), is preserved by reads (ghost layer untouched) and signs
(banked (a) raises the charge by `≤ (attempts)·ε`, matching the enncard growth of
`ghostChargeK`). It is only an *averaged* fact — pointwise per state it is false, since a
single ghost entry costs `1`, not `ε`. -/
def ghostChargeInv (ε : ℝ) (ν : GhostState M Commit Chal → ℝ≥0∞) : Prop :=
  ∀ mc : M × Commit,
    (∑' p : GhostState M Commit Chal, ν p * memCharge M p.1.1.2 mc)
      ≤ ghostChargeK M ν * ENNReal.ofReal ε

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- A step that never writes the ghost layer and preserves the bad flag (uniform forward, or a
signing step — whose handler leaves `s.2` untouched) preserves the per-state expected bad
mass: the post-step flag equals the pre-step flag with probability one (mass `≤ 1`). -/
lemma ghostHybridImpl_flag_preserved_le {γ : Type}
    (run : ProbComp (γ × GhostState M Commit Chal)) (p : GhostState M Commit Chal)
    (hflag : ∀ z ∈ support run, z.2.2 = p.2) :
    (∑' z : γ × GhostState M Commit Chal, Pr[= z | run] * (if z.2.2 = true then 1 else 0))
      ≤ (if p.2 = true then 1 else 0) := by
  classical
  calc (∑' z : γ × GhostState M Commit Chal, Pr[= z | run] * (if z.2.2 = true then 1 else 0))
      = ∑' z : γ × GhostState M Commit Chal, Pr[= z | run] * (if p.2 = true then 1 else 0) := by
        refine tsum_congr fun z => ?_
        by_cases hz : z ∈ support run
        · rw [hflag z hz]
        · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
    _ = (∑' z : γ × GhostState M Commit Chal, Pr[= z | run]) * (if p.2 = true then 1 else 0) := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ (if p.2 = true then 1 else 0) :=
        mul_le_of_le_one_left zero_le' tsum_probOutput_le_one

omit [SampleableType Stmt] in
/-- Per-state read-step bad-mass bound: the eager read sets the bad flag only on a ghost hit,
so the expected post-step bad mass is at most the pre-step flag plus the membership charge of
the read target. -/
lemma ghostHybridImpl_read_expected_flag_le (pk : Stmt) (sk : Wit)
    (mc : M × Commit) (p : GhostState M Commit Chal) :
    (∑' z : Chal × GhostState M Commit Chal,
        Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
          (if z.2.2 = true then 1 else 0))
      ≤ (if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc := by
  classical
  -- On a miss the post-step flag is preserved; on a hit it is forced true. In both cases the
  -- post-step flag is `≤ p.2 ∨ (ghost hit at mc)` — captured by `memCharge`.
  have hflag : ∀ z ∈ support ((ghostHybridImpl ids M maxAttempts true pk sk
      (.inl (.inr mc))).run p),
      (if z.2.2 = true then (1 : ℝ≥0∞) else 0)
        ≤ (if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc := by
    intro z hz
    simp only [ghostHybridImpl, StateT.run_mk] at hz
    rcases hgh : p.1.1.2 mc with _ | v
    · -- Miss: flag preserved, `memCharge = 0`.
      simp only [hgh, support_map] at hz
      obtain ⟨cu, -, rfl⟩ := hz
      exact le_add_right le_rfl
    · -- Hit: flag forced true, `memCharge = 1`.
      simp only [hgh, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      rw [show memCharge M p.1.1.2 mc = 1 by simp [memCharge, hgh]]
      exact le_add_self
  calc (∑' z : Chal × GhostState M Commit Chal,
          Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
            (if z.2.2 = true then 1 else 0))
      ≤ ∑' z : Chal × GhostState M Commit Chal,
          Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
            ((if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc) := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : z ∈ support ((ghostHybridImpl ids M maxAttempts true pk sk
            (.inl (.inr mc))).run p)
        · gcongr; exact hflag z hz
        · refine le_of_eq (mul_eq_zero.mpr (Or.inl ?_)) |>.trans zero_le'
          exact probOutput_eq_zero_of_not_mem_support hz
    _ = (∑' z : Chal × GhostState M Commit Chal,
          Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p]) *
          ((if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc) := by
        rw [ENNReal.tsum_mul_right]
    _ ≤ (if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc :=
        mul_le_of_le_one_left zero_le' tsum_probOutput_le_one

omit [SampleableType Stmt] in
/-- **`h_carry` premise of the threaded bound for the ghost handler.** The carried bad mass
telescopes across one step, paying the read hit charge `≤ K ν · ofReal ε` on a read step
(via the invariant `ghostChargeInv`). Uniform/sign steps preserve the carried bad mass. -/
lemma avgBadM_ghostHybridImpl_threaded_carry
    (ε p_abort : ℝ) (_hp₀ : 0 ≤ p_abort) (_hp : p_abort < 1) (_hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (_hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (_hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (ν : GhostState M Commit Chal → ℝ≥0∞)
    (_hInv : ghostChargeInv M ε ν)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) :
    (∑' u : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t,
        ∑' p : GhostState M Commit Chal,
          OracleComp.ProgramLogic.Relational.postStepOutM
            (ghostHybridImpl ids M maxAttempts true pk sk) ν t u p *
            (if p.2 = true then 1 else 0))
      ≤ (∑' p : GhostState M Commit Chal, ν p * (if p.2 = true then 1 else 0)) +
          (if (t matches Sum.inl (Sum.inr _)) then
            ghostChargeK M ν * ENNReal.ofReal ε else 0) := by
  classical
  -- Rewrite the telescoped carried-bad mass as the weighted post-step bad mass.
  rw [OracleComp.ProgramLogic.Relational.tsum_tsum_postStepOutM_mul
    (ghostHybridImpl ids M maxAttempts true pk sk) ν t (fun s => if s.2 = true then 1 else 0)]
  rcases t with (n | mc) | msg
  · -- Uniform step: flag preserved.
    rw [if_neg (by simp), add_zero]
    refine ENNReal.tsum_le_tsum fun p => ?_
    gcongr
    refine ghostHybridImpl_flag_preserved_le M _ p ?_
    intro z hz
    simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz; rfl
  · -- Read step: pays the per-target membership charge, bounded via the invariant by `K ν · ε`.
    rw [if_pos (by simp)]
    calc (∑' p : GhostState M Commit Chal, ν p *
            ∑' z : Chal × GhostState M Commit Chal,
              Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk (.inl (.inr mc))).run p] *
                (if z.2.2 = true then 1 else 0))
        ≤ ∑' p : GhostState M Commit Chal, ν p *
            ((if p.2 = true then 1 else 0) + memCharge M p.1.1.2 mc) :=
          ENNReal.tsum_le_tsum fun p => by
            gcongr
            exact ghostHybridImpl_read_expected_flag_le ids M maxAttempts pk sk mc p
      _ = (∑' p : GhostState M Commit Chal, ν p * (if p.2 = true then 1 else 0)) +
            ∑' p : GhostState M Commit Chal, ν p * memCharge M p.1.1.2 mc := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun p => by rw [mul_add]
      _ ≤ (∑' p : GhostState M Commit Chal, ν p * (if p.2 = true then 1 else 0)) +
            ghostChargeK M ν * ENNReal.ofReal ε := by
          gcongr
          exact _hInv mc
  · -- Sign step: the signing handler leaves `s.2` untouched, so the flag is preserved.
    rw [if_neg (by simp), add_zero]
    refine ENNReal.tsum_le_tsum fun p => ?_
    gcongr
    refine ghostHybridImpl_flag_preserved_le M _ p ?_
    intro z hz
    simp only [ghostHybridImpl, StateT.run_mk, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz; rfl

omit [SampleableType Stmt] in
/-- **`h_K` premise of the threaded bound for the ghost handler.** The ghost-size accumulator
`ghostChargeK` telescopes across one step, growing by `≤ ofReal (1/(1-p)) · mass ν` on a sign
step (banked (a)/(c)); reads and uniform steps preserve it (the ghost layer is untouched). -/
lemma avgBadM_ghostHybridImpl_threaded_K
    (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (_hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (_hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (ν : GhostState M Commit Chal → ℝ≥0∞)
    (_hInv : ghostChargeInv M ε ν)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) :
    (∑' u : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t,
        ghostChargeK M
          (OracleComp.ProgramLogic.Relational.postStepOutM
            (ghostHybridImpl ids M maxAttempts true pk sk) ν t u))
      ≤ ghostChargeK M ν +
          (if (t matches Sum.inr _) then
            ENNReal.ofReal (1 / (1 - p_abort)) *
              (∑' p : GhostState M Commit Chal, ν p) else 0) := by
  classical
  -- Rewrite `∑'u K(postStepOutM ν t u)` as the weighted post-step charge
  -- for `F := enncard ∘ ghost`.
  have hrw : (∑' u : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range t,
        ghostChargeK M
          (OracleComp.ProgramLogic.Relational.postStepOutM
            (ghostHybridImpl ids M maxAttempts true pk sk) ν t u))
      = ∑' p : GhostState M Commit Chal, ν p *
          ∑' z : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × GhostState M Commit Chal,
            Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk t).run p] *
              QueryCache.enncard (z.2.1.1.2) := by
    rw [← OracleComp.ProgramLogic.Relational.tsum_tsum_postStepOutM_mul
      (ghostHybridImpl ids M maxAttempts true pk sk) ν t (fun s => QueryCache.enncard s.1.1.2)]
    rfl
  rw [hrw, ghostChargeK]
  -- Per-state inner charge bound, then `tsum`-monotone fold.
  rcases t with (n | mc) | msg
  · -- Uniform step: state untouched, ghost charge preserved.
    rw [if_neg (by simp), add_zero]
    refine ENNReal.tsum_le_tsum fun p => ?_
    exact le_of_eq (congrArg (ν p * ·)
      (ghostHybridImpl_unif_expected_enncard ids M maxAttempts pk sk n p))
  · -- Read step: writes only the base layer, ghost charge preserved.
    rw [if_neg (by simp), add_zero]
    refine ENNReal.tsum_le_tsum fun p => ?_
    exact le_of_eq (congrArg (ν p * ·)
      (ghostHybridImpl_read_expected_enncard ids M maxAttempts pk sk mc p))
  · -- Sign step: ghostSignBody grows the ghost size by `≤ ∑ attempts ≤ 1/(1-p)`.
    rw [if_pos (by simp)]
    rw [mul_comm (ENNReal.ofReal (1 / (1 - p_abort))) _, ← ENNReal.tsum_mul_right,
      ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun p => ?_
    rw [← mul_add]
    gcongr
    exact ghostHybridImpl_sign_expected_enncard_le ids M maxAttempts pk sk msg hAbort hp₀ hp p

/-! ## Measure-level eager↔lazy coupling engine

`avgBadM_eager_le_lazy_joint` is a banked, axiom-clean, reusable free-monad telescoping
engine for dominating averaged bad masses under a two-measure coupling invariant. It is not
currently on the live path of the #228 ghost-read bound (the live path goes through the sound
M1→M2→M3 ghost-blind factorization route). It is retained here as general infrastructure for
a future joint-law approach to the eager↔lazy comparison.

The engine carries a **two-measure coupling invariant** `Inv νe νl` through the free-monad
induction on `oa`: the uniform and signing steps preserve `Inv` on the per-output post-step
measures (the handlers are definitionally identical on those steps, so `postStepOutM` agrees
and `Inv` is threaded unchanged), the pure leaf compares the carried bad mass under `Inv`, and
the read step supplies the genuine deferred-sampling inequality — the eager read's averaged
ghost-hit marginal over `νe` dominated by the lazy read's deferred-fire marginal over `νl`.

A per-state (single-measure, `νe = νl`) version of the read inequality is **false** — at a
committed ghost-hit state the eager read flips the bad flag with mass `1` while the lazy read
fires with sub-unit mass — so the two-measure coupling is essential for any future application. -/

omit [SampleableType Stmt] in
/-- **Two-measure eager↔lazy averaged-bad coupling engine.** Threads a coupling invariant
`Inv : (state-measure) → (state-measure) → Prop` through the free-monad induction on `oa`:

* `h_step_eq`: a non-read step (uniform forward or signing query) preserves `Inv` on the
  per-output post-step measures. The eager and lazy handlers are definitionally identical on
  these steps, so the two `postStepOutM` measures are produced by the same map and `Inv` is
  threaded across them.
* `h_pure`: at a pure leaf the carried bad mass of `νe` is dominated by that of `νl` (under
  `Inv`).
* `h_read`: at a random-oracle read step, the eager read's averaged ghost-hit bad marginal
  over `νe` is dominated by the lazy read's deferred-fire marginal over `νl` (under `Inv`),
  with the invariant-conditional inductive hypothesis on the continuations available.

Given these, `avgBadM eager νe oa ≤ avgBadM lazy νl oa` for every `Inv`-related pair. This is
the measure-level coupling vehicle: the read-step averaging (signing-time draw into `νe`
versus read-time redraw of `νl`) is exactly what the per-output post-step *measures* (not
per-state Diracs) carry, which is why a per-state comparison cannot replace it. -/
lemma avgBadM_eager_le_lazy_joint (pk : Stmt) (sk : Wit)
    (Inv : (GhostState M Commit Chal → ℝ≥0∞) → (GhostState M Commit Chal → ℝ≥0∞) → Prop)
    (h_step_eq : ∀ (νe νl : GhostState M Commit Chal → ℝ≥0∞), Inv νe νl →
      ∀ (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain),
        (¬ t matches Sum.inl (Sum.inr _)) →
        ∀ u, Inv (OracleComp.ProgramLogic.Relational.postStepOutM
                (ghostHybridImpl ids M maxAttempts true pk sk) νe t u)
              (OracleComp.ProgramLogic.Relational.postStepOutM
                (lazyGhostHybridImpl ids M maxAttempts pk sk) νl t u))
    (h_read : ∀ (νe νl : GhostState M Commit Chal → ℝ≥0∞), Inv νe νl →
      ∀ (mc : M × Commit)
        (cont : Chal → OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))) (M × Option (Commit × Resp))),
        (∀ u νe' νl', Inv νe' νl' →
          OracleComp.ProgramLogic.Relational.avgBadM
              (ghostHybridImpl ids M maxAttempts true pk sk) νe' (cont u)
            ≤ OracleComp.ProgramLogic.Relational.avgBadM
              (lazyGhostHybridImpl ids M maxAttempts pk sk) νl' (cont u)) →
        (∑' p : GhostState M Commit Chal, νe p *
            ∑' z : Chal × GhostState M Commit Chal,
              Pr[= z | (ghostHybridImpl ids M maxAttempts true pk sk
                  (Sum.inl (Sum.inr mc))).run p] *
                Pr[ fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal =>
                    w.2.2 = true |
                  (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (cont z.1)).run z.2])
          ≤ ∑' p : GhostState M Commit Chal, νl p *
            ∑' z : Chal × GhostState M Commit Chal,
              Pr[= z | (lazyGhostHybridImpl ids M maxAttempts pk sk
                  (Sum.inl (Sum.inr mc))).run p] *
                Pr[ fun w : (M × Option (Commit × Resp)) × GhostState M Commit Chal =>
                    w.2.2 = true |
                  (simulateQ (lazyGhostHybridImpl ids M maxAttempts pk sk) (cont z.1)).run z.2])
    (h_pure : ∀ (νe νl : GhostState M Commit Chal → ℝ≥0∞), Inv νe νl →
      ∀ _x : M × Option (Commit × Resp),
        (∑' p : GhostState M Commit Chal, νe p * (if p.2 = true then 1 else 0))
            ≤ ∑' p : GhostState M Commit Chal, νl p * (if p.2 = true then 1 else 0))
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (M × Option (Commit × Resp))) :
    ∀ νe νl : GhostState M Commit Chal → ℝ≥0∞, Inv νe νl →
      OracleComp.ProgramLogic.Relational.avgBadM
          (ghostHybridImpl ids M maxAttempts true pk sk) νe oa
        ≤ OracleComp.ProgramLogic.Relational.avgBadM
          (lazyGhostHybridImpl ids M maxAttempts pk sk) νl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      intro νe νl hInv
      rw [OracleComp.ProgramLogic.Relational.avgBadM_pure,
        OracleComp.ProgramLogic.Relational.avgBadM_pure]
      exact h_pure νe νl hInv x
  | @query_bind t cont ih =>
      intro νe νl hInv
      rcases t with (n | mc) | msg
      · rw [OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output,
          OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output]
        refine ENNReal.tsum_le_tsum fun u => ?_
        exact ih u _ _ (h_step_eq νe νl hInv (Sum.inl (Sum.inl n)) (by simp) u)
      · rw [OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq,
          OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq]
        exact h_read νe νl hInv mc cont (fun u νe' νl' h => ih u νe' νl' h)
      · rw [OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output,
          OracleComp.ProgramLogic.Relational.avgBadM_query_bind_eq_tsum_output]
        refine ENNReal.tsum_le_tsum fun u => ?_
        exact ih u _ _ (h_step_eq νe νl hInv (Sum.inr msg) (by simp) u)

omit [SampleableType Stmt] in
/-- **M1: the identical-until-bad / ghost-blind reduction** (foundational step of the sound
#228 ghost-read bound). The eager hybrid handler `ghostHybridImpl … true` and the ghost-blind
handler `ghostBlindImpl` flip the adversarial-read bad flag with *exactly the same*
probability at the empty-cache Dirac start:

`Pr[bad | (simulateQ (ghostHybridImpl … true) (adv.main pk)).run δ_∅]`
`  = Pr[bad | (simulateQ ghostBlindImpl (adv.main pk)).run δ_∅]`.

The two handlers are *identical until bad*: they coincide on uniform queries, on signing
queries, and on ghost-*miss* reads (all run the same `roStep` / `ghostSignBody`), and on a
ghost-*hit* read both flip the bad flag (`ghostBlindImpl_agree_good`), while neither ever
unsets it (`ghostHybridImpl_bad_mono` / `ghostBlindImpl_bad_mono`). The blind handler answers
a hit from the real layer instead of returning the ghost value, so the ghost-key values never
influence the run — they are consulted only to record the would-hit. Because the runs differ
only on the already-bad trajectory (where both flags read `true`), the bad marginals coincide,
by the banked exact identical-until-bad bad-event equality
`probEvent_output_bad_eq'`. -/
lemma probEvent_ghostHybridImpl_bad_eq_ghostBlind (pk : Stmt) (sk : Wit) :
    Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      = Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)] :=
  OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
    (ghostHybridImpl ids M maxAttempts true pk sk)
    (ghostBlindImpl ids M maxAttempts pk sk)
    (ghostBlindImpl_agree_good ids M maxAttempts pk sk)
    (ghostHybridImpl_bad_mono ids M maxAttempts true pk sk)
    (ghostBlindImpl_bad_mono ids M maxAttempts pk sk)
    (adv.main pk) (((∅, ∅), []) : _)

omit [SampleableType Stmt] in
/-- **M1 (≤ form).** The eager ghost-read bad mass is bounded by the ghost-blind handler's
bad mass at the empty-cache Dirac start; immediate from the equality
`probEvent_ghostHybridImpl_bad_eq_ghostBlind`. This is the reduction the sound #228 spine
chains with M2 (reads ⊥ ghost-key values) and M3 (geometric first-fire charge). -/
lemma probEvent_ghostHybridImpl_bad_le_ghostBlind (pk : Stmt) (sk : Wit) :
    Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ Pr[ fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)] :=
  (probEvent_ghostHybridImpl_bad_eq_ghostBlind ids hr M maxAttempts adv pk sk).le

/-! ### M3: the geometric first-fire charge (assembly)

`probEvent_ghostBlind_bad_le_of_fac` is the **M3** charge: given the **M2** deferred-sampling
factorization `hfac` — the ghost-blind run's bad marginal exhibited as the value-free
multi-key hidden-target game `kn >>= hiddenReadList (Prod.fst <$> ids.commit pk sk) (qH+1) σ`
(rejected commitment values deferred to a front block, read off by the adversary's adaptive
all-miss strategy `σ`) — the target bound `qS·(qH+1)·ε/(1-p)` follows by the banked
union-bound + geometric-fold pipeline:

* per-target guessing bound `hGuess` (raw `Pr[= w | commit] ≤ ε`) feeds the multi-key
  first-fire union bound `OracleComp.probEvent_bind_hiddenReadList_le`, giving
  `E[n]·((qH+1)·ε)` where `E[n] = ∑' n, Pr[= n | kn]·n` is the expected ghost-key count;
* the expected-count mean bound `hmean` (`E[n] ≤ qS/(1-p)`, the aggregate of
  `tsum_probOutput_commit_mul_abort_le` over the `qS` signing queries) folds into the target
  via `hiddenReadList_fold_le_target`.

The `Pr[reject|mc] ≤ 1` skew-drop is already baked into the raw-`commit` per-target bound
`hGuess` (the hidden targets are drawn from the *raw* commit law, not the rejection-conditioned
law), so no skew survives into this charge. The accepting attempt contributes `0` because it
is not a rejected draw and so is absent from `kn`'s key count. -/
omit [SampleableType Stmt] in
theorem probEvent_ghostBlind_bad_le_of_fac
    (qS qH : ℕ) (ε p_abort : ℝ) (hp : p_abort < 1)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (σ : List Bool → Commit) (kn : ProbComp ℕ)
    (hmean : ∑' n : ℕ, Pr[= n | kn] * (n : ℝ≥0∞)
      ≤ ENNReal.ofReal ((qS : ℝ) / (1 - p_abort)))
    (hfac : Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ Pr[(fun b : Bool => b = true) |
        kn >>= fun n => OracleComp.hiddenReadList (Prod.fst <$> ids.commit pk sk) (qH + 1) σ n]) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  refine (OracleComp.probEvent_le_of_eq_bind_hiddenReadList (oa := Prod.fst <$> ids.commit pk sk)
    (ε := ENNReal.ofReal ε) hGuess (qH + 1) σ kn hfac).trans ?_
  -- The averaged union bound `E[n]·((qH+1)·ε)` folds into the target via the geometric fold.
  refine le_trans (le_of_eq ?_)
    (hiddenReadList_fold_le_target qS qH ε p_abort hp (fun n => Pr[= n | kn]) hmean)
  -- Reconcile the `((qH+1)·ofReal ε)` factor shapes: `((qH:ℝ≥0∞)+1)` vs `↑(qH+1)`.
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [mul_assoc]
  congr 2
  push_cast
  ring

omit [SampleableType Stmt] in
/-- **Ghost-blind read-step bad indicator** (an M2 structural building block). Starting from a
state with the bad flag unset, the ghost-blind handler's adversarial random-oracle read at `mc`
sets the bad flag with mass exactly `1` if `mc` lies in the ghost-cache domain and `0`
otherwise. Identical indicator to the eager handler's `probOutput_ghostHybridImpl_read_bad`, but
here the *answer* is `roStep` on the real layer in **both** branches (hit and miss): the ghost
value never reaches the output, only the bad flag records the structural hit. This is the
manifest output-irrelevance of `ghostBlindImpl` at the read step — the per-read membership test
the M2 factorization reads off as a `hiddenReadList` probe. -/
lemma probEvent_ghostBlindImpl_read_bad (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) × List M) :
    Pr[fun z : Chal × GhostState M Commit Chal => z.2.2 = true |
        (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run (s, false)] =
      if s.1.2 mc = none then 0 else 1 := by
  rw [ghostBlindImpl_eq_ghostHybridImpl_false]
  cases hgh : s.1.2 mc with
  | some v =>
      rw [ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk hgh]
      simp
  | none =>
      rw [ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk hgh, if_pos rfl]
      simp [probEvent_eq_zero]

/-! ### Stage 2: single-query deferral primitives

The value-free foundation (`blindStepProj_map_ghostBlindImpl_indep`, Stage 1) shows the stored
ghost commitment values never feed back into the ghost-blind run. The two lemmas here are the
*single-query* deferral atoms that Stage 3 instantiates once per rejected signing attempt:

* `ghostBlindImpl_read_singletonGhost_bad` connects the ghost-blind read handler to the
  membership predicate. With the ghost cache holding a single rejected-attempt key `(msg, w) ↦ c`,
  an adversarial read at `mc` fires the bad flag *exactly* when `mc = (msg, w)` — the structural
  read-hit test that `OracleComp.readMany` models for one hidden target.
* `ghostBlind_singleDraw_fire_le` is the commit-sampler instance of the deferral primitive
  `OracleComp.probEvent_bind_fire_le_of_gen`: a run that draws one ghost commitment up front and
  feeds it *only* through the fixed `q`-read game of a value-free generator fires with probability
  at most `q · ε`. This is the "front-loaded one draw" charge; Stage 3 supplies the value-free
  generator `gen` from `blindStepProj_map_ghostBlindImpl_indep` and folds the `qS` per-query
  charges into the aggregate `kn >>= drawList` block. -/

omit [SampleableType Stmt] in
/-- **Stage 2 read-membership atom.** With the ghost cache holding exactly the single
rejected-attempt key `(msg, w) ↦ c`, an adversarial random-oracle read at `mc` in the ghost-blind
run fires the bad flag with mass `1` when `mc = (msg, w)` and `0` otherwise. This is the structural
single-target read-hit indicator (`OracleComp.readMany`'s per-read test) realised by the
ghost-blind handler: the value `w` enters the run *only* through this membership test, never through
the read's answer (which is `roStep` on the real layer — `probEvent_ghostBlindImpl_read_bad`). -/
lemma ghostBlindImpl_read_singletonGhost_bad (pk : Stmt) (sk : Wit) (mc : M × Commit) (msg : M)
    (w : Commit) (c : Chal) (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    Pr[fun z : Chal × GhostState M Commit Chal => z.2.2 = true |
        (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run
          (((re, (∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery (msg, w) c), l), false)] =
      if mc = (msg, w) then 1 else 0 := by
  rw [probEvent_ghostBlindImpl_read_bad ids M maxAttempts pk sk mc
    ((re, (∅ : (M × Commit →ₒ Chal).QueryCache).cacheQuery (msg, w) c), l)]
  by_cases h : mc = (msg, w)
  · subst h
    rw [if_neg (by simp), if_pos rfl]
  · rw [if_pos (by simp [QueryCache.cacheQuery_of_ne _ _ h]), if_neg h]

omit [SampleableType Stmt] [SampleableType Chal] in
/-- **Stage 2 single-query deferral.** A run that draws one ghost commitment
`w ← Prod.fst <$> ids.commit pk sk` (each outcome of mass at most `ε`) and feeds it to a
*value-free* continuation `k w = gen >>= fun p => pure (p.1, readMany w q p.2)` — a `w`-free
generator `gen` producing the visible output `p.1` and the `q`-read strategy `p.2`, with the drawn
commitment entering *only* through the fixed read game `readMany w q p.2` — fires with probability
at most `q · ε`.

This is the commit-sampler instance of `OracleComp.probEvent_bind_fire_le_of_gen`. The hypothesis
`hk` is exactly the value-freeness supplied by `blindStepProj_map_ghostBlindImpl_indep` (Stage 1):
because the ghost value never influences the run, the continuation's fire-marginal factors through
a `w`-free generator with the draw confined to the read-membership test
(`ghostBlindImpl_read_singletonGhost_bad`). Stage 3 instantiates this once per rejected attempt. -/
lemma ghostBlind_singleDraw_fire_le {α : Type} (pk : Stmt) (sk : Wit) {ε : ℝ≥0∞}
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ε)
    (q : ℕ) (gen : ProbComp (α × (List Bool → Commit))) (k : Commit → ProbComp (α × Bool))
    (hk : ∀ w : Commit, k w = gen >>= fun p => pure (p.1, OracleComp.readMany w q p.2)) :
    Pr[(fun z : α × Bool => z.2 = true) | (Prod.fst <$> ids.commit pk sk) >>= k]
      ≤ (q : ℝ≥0∞) * ε :=
  OracleComp.probEvent_bind_fire_le_of_gen hGuess q gen k hk

/-! ### M2: the deferred-sampling factorization (the single open obligation)

The **M2** content is the ghost-blind run's bad marginal *factoring* as a value-free deferred-draw
game. This is the crux of the sound route and is the single open obligation; it is genuinely
multi-week-class. The headline charges it through the σ-free first-moment residual
`readRecord_expected_coincidences_le` (the expected coincidence count of the value-free recorded
read-commit list with the recorded rejected draws).

Why it factors (the sound argument). In `ghostBlindImpl` an adversarial random-oracle read at a
ghost-cache hit answers from the *real* layer via `roStep` — identically to a miss — and only
*records* the would-hit by flipping the bad flag (`ghostBlindImpl_eq_ghostHybridImpl_false`,
`ghostBlindImpl_agree_good`). So the ghost-cache *values* are write-only side-data: they never
influence the run's outputs or continuation. Consequently the run's joint law of (adversary read
points, reject pattern / loop lengths, real cache) is produced by a value-free run that is
*independent of the stored commitment values*; those values are drawn `~ Prod.fst <$> ids.commit`
per *rejected* attempt and gated into the ghost cache by the reject decision.

Formalize as a deferred-sampling factorization: pull every rejected attempt's commitment draw
into the recorded drawn-list of the deferred handler `deferredDrawReadImpl`, independent of the
value-free recorded read-commit list. The expected coincidence count is then bounded by
`(#reads) · (#draws) · (max draw mass) ≤ (qH+1) · ε · E[#attempts]`, with `E[#attempts] ≤
qS/(1-p)` the aggregate of `tsum_probOutput_commit_mul_abort_le` over the `qS` signing queries
(each rejected attempt is reached with geometric probability, summed by `geomAttemptSum_le`).

Banked tools for the eventual discharge: the read-marginal equalities
`probEvent_ghostHybridImpl_read_bad_single_eq_lazyFire` /
`probOutput_eagerMultiReadBad_eq_lazyFire_or` (the signing-time→read-time draw commutation, here
applied to the value-free `ghostBlindImpl` continuation rather than the eager one whose
continuation depends on the read value), `probOutput_lazyGhostFire_one`, and the value-free
read-answer agreement (`ghostBlindImpl`'s hit branch is `roStep`, the same `map`-of-`roStep` as a
miss and as the lazy handler). The crux is lifting the output-irrelevance through the `simulateQ`
fold so that the per-rejected-attempt draws commute to the front independently of the intervening
adversary computation.

This factorization route is sound precisely because `ghostBlindImpl` reads never feed the ghost
value into the run, so the draws are genuinely deferrable. -/

/-! ### Stage 3a: deferred-handler ingredients

The sound first-moment route couples the eager ghost-blind run to a *deferred* handler `impl₂` (a
genuine `QueryImpl`) via a per-step coupling relation `Rrun` on the two run distributions and the
two bad predicates `bad₁ / bad₂`. This block constructs those ingredients.

The deferred handler `deferredDrawImpl` carries, instead of eager-committed ghost keys, the
*accumulated list of drawn rejected-attempt commitments* (the front block, grown lazily as sign
steps draw) together with the real cache, the signed list, and the "some recorded read hit a drawn
commitment" flag. Its state is

  `DeferredState M Commit Chal :=
    (((M × Commit →ₒ Chal).QueryCache × List M) × List Commit) × Bool`.

Branch behaviour, designed so that the *observable* component (output, real cache, signed list)
coincides with the ghost-blind handler value-free (Stage 1):
* a **uniform** query forwards exactly as `ghostBlindImpl` does, touching neither the drawn list nor
  the bad flag;
* a **random-oracle read** answers from the real layer via `roStep` (identical read point and answer
  to `ghostBlindImpl`'s value-free hit/miss branches) and sets the bad flag iff the read point's
  commitment `mc.2` is among the accumulated drawn list — the deferred counterpart of the eager
  membership test against the ghost domain;
* a **signing** query runs the value-free signing body (`run_ghostSignBody_fst` recovers
  `transSignBody`, the accepted-only loop) for the output and real cache, and appends to the drawn
  list one i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw per rejected attempt, mirroring the eager
  ghost writes. -/

/-- State of the deferred-draw handler: real cache, signed-message list, the accumulated list of
drawn rejected-attempt commitments (the deferral front block), and the monotone "some recorded read
hit a drawn commitment" flag. The drawn list replaces the eager ghost cache: where `ghostBlindImpl`
commits sampled keys into its ghost layer, `deferredDrawImpl` only records the *list* of drawn
commitments, which is later read off as the front `drawList` block. -/
abbrev DeferredState (M Commit Chal : Type) : Type :=
  (((M × Commit →ₒ Chal).QueryCache × List M) × List Commit) × Bool

/-- Draw-collecting signing body: mirrors `ghostSignBody` but threads only the *real* cache and
accumulates the list of drawn *rejected*-attempt commitments instead of writing them to a ghost
layer. Returns `(output, drawn commits this query)`. Only the rejected-attempt commitments are
recorded, in attempt order; the accepted attempt (whose commitment is returned to the caller and
cached in the real layer) records nothing, exactly mirroring `ghostSignBody`, whose ghost layer
holds the rejected commitments and `uncacheQuery`-s the accepted one. Forgetting the drawn list
recovers `transSignBody` (the value-free output and real cache), and the drawn list is exactly the
list of i.i.d. raw `Prod.fst <$> ids.commit pk sk` samples taken on the *rejected* attempts — the
value-free side-data that never feeds back into the run's outputs. -/
noncomputable def ghostSignDrawBody (pk : Stmt) (sk : Wit) (msg : M) :
    ℕ → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp) × List Commit)
  | 0 => pure (none, [])
  | n + 1 => do
    let (w, st) ← liftM (ids.commit pk sk)
    let c ← (liftM (uniformSample Chal) :
      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp Chal)
    let oz ← liftM (ids.respond pk sk st c)
    match oz with
    | some z =>
        modify fun cache => cache.cacheQuery (msg, w) c
        pure (some (w, z), [])
    | none =>
        let (res, ws) ← ghostSignDrawBody pk sk msg n
        pure (res, w :: ws)

omit [SampleableType Stmt] in
/-- One-step unfolding of the draw-collecting signing body, mirroring `run_ghostSignBody_succ`.
The body draws a commitment `w`, samples a challenge `ch`, responds, and on accept records *no*
drawn commitment (the accepted commit is returned, not deferred) while on reject prepends `w` to
the recursively collected list of rejected commitments. -/
lemma run_ghostSignDrawBody_succ (pk : Stmt) (sk : Wit) (msg : M) (n : ℕ)
    (re : (M × Commit →ₒ Chal).QueryCache) :
    (ghostSignDrawBody ids M pk sk msg (n + 1)).run re =
      ids.commit pk sk >>= fun ws =>
        uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re := by
  simp only [ghostSignDrawBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
    pure_bind]
  refine congrArg (ids.commit pk sk >>= ·) (funext fun ws => ?_)
  obtain ⟨w, st⟩ := ws
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => simp [StateT.run_modify]
  | none => simp [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp]

/-! ### Body-level tape resampling (the per-body half of the tape factorization)

The draw-collecting signing body `ghostSignDrawBody` draws each attempt's commitment *inline*. The
genuine fold-lift content of the ghost-read bound is to front-load every interleaved per-attempt
draw into one independent block, so the drawn *values* factor away from the value-free adversarial
read points. The body-level half of that program — recasting one signing body's inline draws as
consumption from a *pre-drawn* tape — is proved here as a distributional equality
`evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody`:

`𝒟[(ghostSignDrawBody … n).run re] = 𝒟[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`.

Pre-drawing the `n`-block of full `(Commit × PrvState)` commitment draws and consuming them
head-first (`tapeSignBody`) is distributionally identical to drawing them inline: the control flow
(accept/reject, via the inline `uniformSample`/`respond`) reads the *same* tape values, and the
unused suffix on an early accept is discarded. The proof is a structural induction on `n` that, at
each attempt, commutes the recursive front block `drawList n` past the inline
`uniformSample`/`respond` draws (`evalDist_bind_comm_probComp`, the i.i.d. resampling step) and
matches the reject-branch recursion to the inductive hypothesis.

This is the local, tractable `bind`-commutation; the remaining open content of
`readRecord_expected_pairs_le` is to lift it across the *opaque adversary* `simulateQ (oa)` fold:
the interleaved per-query draw blocks all commuting to the front, past the adaptive read points. -/

/-- **i.i.d. bind-commutation at the distribution level for `ProbComp`.** Two independent draws
`oa`, `ob` feeding a common continuation `k` may be drawn in either order without changing the
output distribution. The `OracleComp` monad is *not* commutative as a free monad (its `bind` is
syntactic), but its `evalDist` image into `SPMF` is: the two iterated sums over the independent
draws exchange by `ENNReal.tsum_comm`. This is the local resampling step that front-loads an
output-irrelevant draw past its continuation. -/
theorem evalDist_bind_comm_probComp {α β γ : Type} (oa : ProbComp α) (ob : ProbComp β)
    (k : α → β → ProbComp γ) :
    𝒟[oa >>= fun a => ob >>= fun b => k a b] = 𝒟[ob >>= fun b => oa >>= fun a => k a b] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒟[oa >>= fun a => ob >>= fun b => k a b] x
        = Pr[= x | oa >>= fun a => ob >>= fun b => k a b] from (probOutput_def _ _).symm,
    show 𝒟[ob >>= fun b => oa >>= fun a => k a b] x
        = Pr[= x | ob >>= fun b => oa >>= fun a => k a b] from (probOutput_def _ _).symm]
  rw [probOutput_bind_eq_tsum]
  rw [show (∑' a : α, Pr[= a | oa] * Pr[= x | ob >>= fun b => k a b])
      = ∑' (a : α) (b : β), Pr[= a | oa] * (Pr[= b | ob] * Pr[= x | k a b]) from
    tsum_congr fun a => by rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]]
  rw [probOutput_bind_eq_tsum]
  rw [show (∑' b : β, Pr[= b | ob] * Pr[= x | oa >>= fun a => k a b])
      = ∑' (b : β) (a : α), Pr[= b | ob] * (Pr[= a | oa] * Pr[= x | k a b]) from
    tsum_congr fun b => by rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_left]]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun a => tsum_congr fun b => by ring

/-- **Dropping a never-failing prefix at the distribution level.** A leading draw `od` whose
continuation ignores its value contributes only its total mass; when `od` never fails (mass `1`,
e.g. a `drawList` front block) it can be discarded from the output distribution. -/
theorem evalDist_bind_const_neverFails {α γ : Type} (od : ProbComp α) (hmass : Pr[⊥ | od] = 0)
    (k : ProbComp γ) : 𝒟[od >>= fun _ => k] = 𝒟[k] := by
  refine SPMF.ext fun x => ?_
  rw [show 𝒟[od >>= fun _ => k] x = Pr[= x | od >>= fun _ => k] from (probOutput_def _ _).symm,
    show 𝒟[k] x = Pr[= x | k] from (probOutput_def _ _).symm]
  rw [probOutput_bind_const, hmass]; simp

/-- **Distribution-level congruence under a leading bind.** If two continuations agree as
distributions pointwise then the bound computations agree as distributions. -/
theorem evalDist_bind_congr_left {α β : Type} (oa : ProbComp α) (f g : α → ProbComp β)
    (h : ∀ a, 𝒟[f a] = 𝒟[g a]) : 𝒟[oa >>= f] = 𝒟[oa >>= g] := by
  rw [evalDist_bind, evalDist_bind]; exact congrArg _ (funext h)

/-- **Tape-consuming signing body.** Identical to `ghostSignDrawBody` except that each attempt's
commitment draw `(Commit × PrvState)` is *consumed* from a pre-drawn tape (head-first) instead of
drawn inline. The challenge sampling and response stay inline. On accept the remaining tape suffix
is discarded; an empty tape ends the loop (mirroring budget exhaustion). The recorded
rejected-commit list is built exactly as in `ghostSignDrawBody`. -/
noncomputable def tapeSignBody (pk : Stmt) (sk : Wit) (msg : M) :
    List (Commit × PrvState) → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
      (Option (Commit × Resp) × List Commit)
  | [] => pure (none, [])
  | (w, st) :: rest => do
    let c ← (liftM (uniformSample Chal) :
      StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp Chal)
    let oz ← liftM (ids.respond pk sk st c)
    match oz with
    | some z =>
        modify fun cache => cache.cacheQuery (msg, w) c
        pure (some (w, z), [])
    | none =>
        let (res, ws) ← tapeSignBody pk sk msg rest
        pure (res, w :: ws)

omit [SampleableType Stmt] in
/-- One-step unfolding of the tape-consuming signing body on a non-empty tape, mirroring
`run_ghostSignDrawBody_succ`: the head `(w, st)` is consumed, a challenge sampled and a response
computed; on accept the body records no commitment, on reject it prepends `w` to the recursively
collected list and continues on the tape tail. -/
lemma run_tapeSignBody_cons (pk : Stmt) (sk : Wit) (msg : M) (w : Commit) (st : PrvState)
    (rest : List (Commit × PrvState)) (re : (M × Commit →ₒ Chal).QueryCache) :
    (tapeSignBody ids M pk sk msg ((w, st) :: rest)).run re =
      uniformSample Chal >>= fun ch =>
        ids.respond pk sk st ch >>= fun oz =>
          match oz with
          | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
          | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
              (tapeSignBody ids M pk sk msg rest).run re := by
  simp only [tapeSignBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT, pure_bind]
  refine congrArg (uniformSample Chal >>= ·) (funext fun ch => ?_)
  refine congrArg (ids.respond pk sk st ch >>= ·) (funext fun oz => ?_)
  cases oz with
  | some z => simp [StateT.run_modify]
  | none => simp [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp]

omit [SampleableType Stmt] in
/-- **The body-level tape resampling equality.** Drawing one signing body's `n` attempt
commitments inline (`ghostSignDrawBody`) is distributionally identical to pre-drawing the `n`-block
of full commitment draws into a tape and consuming it head-first (`tapeSignBody`):

`𝒟[(ghostSignDrawBody … n).run re] = 𝒟[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`.

The proof inducts on `n`: at each attempt, the recursive front block `drawList n` is commuted past
the inline `uniformSample`/`respond` draws (the i.i.d. resampling step
`evalDist_bind_comm_probComp`), the accepting branch discards the unused suffix
(`evalDist_bind_const_neverFails`, `drawList` never
fails), and the rejecting branch matches the inductive hypothesis. This is the per-body half of the
tape factorization; lifting it across the opaque adversary fold is the remaining content of
`readRecord_expected_pairs_le`. -/
theorem evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody (pk : Stmt) (sk : Wit) (msg : M)
    (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache) :
    𝒟[(ghostSignDrawBody ids M pk sk msg n).run re] =
      𝒟[OracleComp.drawList (ids.commit pk sk) n >>= fun tape =>
          (tapeSignBody ids M pk sk msg tape).run re] := by
  induction n generalizing re with
  | zero => simp [ghostSignDrawBody, tapeSignBody, OracleComp.drawList]
  | succ n ih =>
      rw [run_ghostSignDrawBody_succ, OracleComp.drawList]
      simp only [bind_assoc, pure_bind]
      rw [evalDist_bind, evalDist_bind]
      refine congrArg (𝒟[ids.commit pk sk] >>= ·) (funext fun ws => ?_)
      obtain ⟨w, st⟩ := ws
      simp only [run_tapeSignBody_cons]
      set dl := OracleComp.drawList (ids.commit pk sk) n with hdl
      have hdlmass : Pr[⊥ | dl] = 0 := by rw [hdl]; exact OracleComp.probFailure_drawList _ _
      rw [show (𝒟[dl >>= fun rest => uniformSample Chal >>= fun ch =>
            ids.respond pk sk st ch >>= fun oz =>
              (match oz with
              | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
              | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                  (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)])
          = 𝒟[uniformSample Chal >>= fun ch => dl >>= fun rest =>
              ids.respond pk sk st ch >>= fun oz =>
                (match oz with
                | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
                | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                    (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)] from
        evalDist_bind_comm_probComp dl (uniformSample Chal) _]
      refine evalDist_bind_congr_left (uniformSample Chal) _ _ (fun ch => ?_)
      rw [show (𝒟[dl >>= fun rest => ids.respond pk sk st ch >>= fun oz =>
            (match oz with
            | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
            | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)])
          = 𝒟[ids.respond pk sk st ch >>= fun oz => dl >>= fun rest =>
              (match oz with
              | some z => pure ((some (w, z), []), re.cacheQuery (msg, w) ch)
              | none => (fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
                  (tapeSignBody ids M pk sk msg rest).run re : ProbComp _)] from
        evalDist_bind_comm_probComp dl (ids.respond pk sk st ch) _]
      refine evalDist_bind_congr_left (ids.respond pk sk st ch) _ _ (fun oz => ?_)
      cases oz with
      | some z => rw [evalDist_bind_const_neverFails dl hdlmass]
      | none =>
          change 𝒟[(fun rws => ((rws.1.1, w :: rws.1.2), rws.2)) <$>
            (ghostSignDrawBody ids M pk sk msg n).run re] = _
          rw [evalDist_map_eq_of_evalDist_eq (ih re)]
          rw [map_eq_bind_pure_comp, bind_assoc]
          refine evalDist_bind_congr_left dl _ _ (fun rest => ?_)
          rw [map_eq_bind_pure_comp]

omit [SampleableType Stmt] in
/-- **Expected drawn-list length of the draw-collecting signing body.** Each attempt of
`ghostSignDrawBody` records exactly one i.i.d. raw `Prod.fst <$> ids.commit pk sk` commitment;
the loop continues only on a fresh-challenge rejection (probability `≤ p` per attempt), so the
expected length of the collected list is at most `∑_{a<n} p ^ a`, the geometric attempt-count
fold (`geomAttemptSum_le`) that bounds the per-signing-query draw count. This is the deferred-draw
counterpart of `tsum_probOutput_run_ghostSignBody_mul_ghost_enncard_le`: the drawn list replaces
the eager ghost layer, so its length plays the role of the ghost-cache size. -/
lemma tsum_probOutput_run_ghostSignDrawBody_mul_length_le (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞)
        ≤ ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a := by
  intro n
  induction n with
  | zero =>
      intro re
      simp only [ghostSignDrawBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro re
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ a with hS
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ a =
          1 + ENNReal.ofReal p_abort * S := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => pow_succ' _ _
      rw [run_ghostSignDrawBody_succ, tsum_probOutput_bind_mul]
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
          ≤ 1 + Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] * S := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
            ≤ 1 + Pr[= none | ids.respond pk sk ws.2 ch] * S := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          have h_oz : ∀ oz : Option Resp,
              (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= z | (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))] * (z.1.2.length : ℝ≥0∞))
              ≤ 1 + (if oz = none then S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), add_zero, tsum_probOutput_pure_mul]
                simp
            | none =>
                rw [if_pos rfl]
                -- length of `ws.1 :: rws.1.2` is `1 + rws.1.2.length`; rewrite map as bind+pure.
                rw [map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
                calc (∑' z : (Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache,
                    Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                      (∑' y : (Option (Commit × Resp) × List Commit) ×
                          (M × Commit →ₒ Chal).QueryCache,
                        Pr[= y | (pure ((fun rws : (Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache =>
                          ((rws.1.1, ws.1 :: rws.1.2), rws.2)) z) :
                          ProbComp ((Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache))] * (y.1.2.length : ℝ≥0∞)))
                    = ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (1 + (z.1.2.length : ℝ≥0∞)) := by
                      refine tsum_congr fun z => ?_
                      rw [tsum_probOutput_pure_mul]
                      simp only [List.length_cons]
                      push_cast
                      ring_nf
                  _ = (∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re]) +
                      ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (z.1.2.length : ℝ≥0∞) := by
                      rw [← ENNReal.tsum_add]
                      exact tsum_congr fun z => by rw [mul_add, mul_one]
                  _ ≤ 1 + S := add_le_add tsum_probOutput_le_one (ih re)
          refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_oz) ?_
          refine add_le_add_right (le_of_eq ?_) _
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by simp [hoz]]
          simp [mul_comm]
        refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ch) ?_
        refine add_le_add_right (le_of_eq ?_) _
        rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      refine le_trans (tsum_probOutput_mul_le_add_of_le _ h_ws) ?_
      rw [hSucc]
      gcongr
      calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            (Pr[= none | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch] * S)
          = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch]) * S := by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun ws => (mul_assoc _ _ _).symm
        _ ≤ ENNReal.ofReal p_abort * S :=
            mul_le_mul_left (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _

omit [SampleableType Stmt] in
/-- **Tight expected drawn-list length of the draw-collecting signing body.** Sharper companion to
`tsum_probOutput_run_ghostSignDrawBody_mul_length_le`: the expected number of *recorded* (rejected)
commitments of one `ghostSignDrawBody` run is at most the *reject-gated* geometric sum
`∑_{a<n} ofReal p^(a+1)` (each summand starts at `p^1`, not `p^0`). The first attempt's commitment
is recorded only on a *rejection* (probability `≤ p`); the accepting attempt records nothing. This
is the tight reject-count bound — `∑_{a<n} p^(a+1) ≤ p/(1-p)` — that the attempt-count law of the
redrafted residual needs: combined with the unconditional `+1` per signing query (the signed-message
list always grows by one), it gives the clean per-query charge `∑_{a≤n} p^a ≤ 1/(1-p)`, whereas the
loose bound `∑_{a<n} p^a` already saturates `1/(1-p)` for the rejects alone and cannot absorb the
extra `+1`. -/
lemma tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight (pk : Stmt) (sk : Wit) (msg : M)
    {p_abort : ℝ}
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      ∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞)
        ≤ ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ (a + 1) := by
  intro n
  induction n with
  | zero =>
      intro re
      simp only [ghostSignDrawBody, StateT.run_pure, tsum_probOutput_pure_mul]
      simp
  | succ n ih =>
      intro re
      classical
      set S : ℝ≥0∞ := ∑ a ∈ Finset.range n, ENNReal.ofReal p_abort ^ (a + 1) with hS
      -- Target: the `(n+1)`-attempt reject-count expectation is `≤ ofReal p * (1 + S)`, which
      -- equals `∑_{a<n+1} ofReal p^(a+1)`.
      have hSucc : ∑ a ∈ Finset.range (n + 1), ENNReal.ofReal p_abort ^ (a + 1)
          = ENNReal.ofReal p_abort * (1 + S) := by
        rw [mul_add, mul_one, hS, Finset.mul_sum, Finset.sum_range_succ', pow_succ, pow_zero,
          one_mul, add_comm]
        congr 1
        exact Finset.sum_congr rfl fun a _ => by rw [← pow_succ']
      rw [hSucc, run_ghostSignDrawBody_succ, tsum_probOutput_bind_mul]
      -- Per-commit-draw `ws`: the recorded list is empty on accept and `ws.1 :: recursive` on
      -- reject; reject happens with probability `Pr[= none | uniformSample >>= respond]`.
      have h_ws : ∀ ws : Commit × PrvState,
          (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= z | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
          ≤ Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] * (1 + S) := by
        intro ws
        rw [tsum_probOutput_bind_mul]
        have h_ch : ∀ ch : Chal,
            (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= z | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (z.1.2.length : ℝ≥0∞))
            ≤ Pr[= none | ids.respond pk sk ws.2 ch] * (1 + S) := by
          intro ch
          rw [tsum_probOutput_bind_mul]
          -- Per response `oz`: accept contributes `0`, reject contributes `1 + S`.
          have h_oz : ∀ oz : Option Resp,
              (∑' z : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= z | (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))] * (z.1.2.length : ℝ≥0∞))
              ≤ (if oz = none then (1 : ℝ≥0∞) + S else 0) := by
            intro oz
            cases oz with
            | some z =>
                rw [if_neg (by simp), tsum_probOutput_pure_mul]
                simp [List.length]
            | none =>
                rw [if_pos rfl, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
                calc (∑' z : (Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache,
                    Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                      (∑' y : (Option (Commit × Resp) × List Commit) ×
                          (M × Commit →ₒ Chal).QueryCache,
                        Pr[= y | (pure ((fun rws : (Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache =>
                          ((rws.1.1, ws.1 :: rws.1.2), rws.2)) z) :
                          ProbComp ((Option (Commit × Resp) × List Commit) ×
                            (M × Commit →ₒ Chal).QueryCache))] * (y.1.2.length : ℝ≥0∞)))
                    = ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (1 + (z.1.2.length : ℝ≥0∞)) := by
                      refine tsum_congr fun z => ?_
                      rw [tsum_probOutput_pure_mul]
                      simp only [List.length_cons]
                      push_cast
                      ring_nf
                  _ = (∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re]) +
                      ∑' z : (Option (Commit × Resp) × List Commit) ×
                        (M × Commit →ₒ Chal).QueryCache,
                      Pr[= z | (ghostSignDrawBody ids M pk sk msg n).run re] *
                        (z.1.2.length : ℝ≥0∞) := by
                      rw [← ENNReal.tsum_add]
                      exact tsum_congr fun z => by rw [mul_add, mul_one]
                  _ ≤ 1 + S := add_le_add tsum_probOutput_le_one (ih re)
          refine le_trans (ENNReal.tsum_le_tsum fun oz =>
            mul_le_mul_right (h_oz oz) _) ?_
          rw [tsum_eq_single (none : Option Resp) fun oz hoz => by
            rw [if_neg hoz, mul_zero]]
          rw [if_pos rfl, mul_comm]
        refine le_trans (ENNReal.tsum_le_tsum fun ch =>
          mul_le_mul_right (h_ch ch) _) ?_
        rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
        exact le_of_eq (tsum_congr fun ch => (mul_assoc _ _ _).symm)
      refine le_trans (ENNReal.tsum_le_tsum fun ws => mul_le_mul_right (h_ws ws) _) ?_
      calc ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            (Pr[= none | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch] * (1 + S))
          = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
              Pr[= none | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch]) * (1 + S) := by
            rw [← ENNReal.tsum_mul_right]
            exact tsum_congr fun ws => (mul_assoc _ _ _).symm
        _ ≤ ENNReal.ofReal p_abort * (1 + S) :=
            mul_le_mul_left (tsum_probOutput_commit_mul_abort_le ids pk sk hAbort) _

omit [SampleableType Stmt] in
/-- **Single-signing-body resampling over-count.** Testing the *drawn list* produced by one
`ghostSignDrawBody` run (the rejected-attempt commitments, write-only side-data) against any *fixed*
read strategy `σ` with `q` reads fires with probability at most testing `n` *fresh* i.i.d. raw
`Prod.fst <$> ids.commit pk sk` draws against the same strategy (`drawList … n`, where `n` is the
attempt budget `maxAttempts`).

This is the genuine per-query resampling content, isolated to one signing body. The drawn list of
the body is *not* equal in law to `n` fresh raw draws (the rejected draws are skewed by the
rejection-conditioning `commit | reject`), but the firing event over-counts to the fresh game: on
the accept branch the body records *no* commitment (so its read-game fires with probability `0`,
dominated by the fresh side, which still draws and tests one value); on the reject branch the body's
recorded commitment is a raw `Prod.fst <$> ids.commit pk sk` draw — distributed exactly as the fresh
head — and its `readMany` test matches the fresh head's, while the recursive rejected list is
dominated by the recursive fresh list (induction). The read strategy `σ` is *fixed* (the read points
are determined by the all-miss reply history; the drawn values never feed them — value-freeness),
which is what lets a single `σ` dominate both sides. Lifting this per-query over-count across the
opaque adversary `simulateQ` fold — front-loading every signing query's interleaved draws into one
aggregate `drawList` block indexed by the run's attempt count — is the remaining fold-level deferral
commute, the same value-free fold-lift isolated in `readRecord_expected_coincidences_le`. This lemma
is a banked single-body over-count partial; it is not on the live headline path (which charges the
expected coincidence count directly). -/
lemma ghostSignDrawBody_readManyList_le_drawList (pk : Stmt) (sk : Wit) (msg : M)
    (q : ℕ) (σ : List Bool → Commit) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache),
      Pr[(fun b : Bool => b = true) |
          (ghostSignDrawBody ids M pk sk msg n).run re >>= fun rws =>
            pure (OracleComp.readManyList rws.1.2 q σ)]
        ≤ Pr[(fun b : Bool => b = true) |
            OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun ws =>
              pure (OracleComp.readManyList ws q σ)] := by
  intro n
  induction n with
  | zero =>
      intro re
      simp [ghostSignDrawBody, OracleComp.drawList, OracleComp.readManyList]
  | succ n ih =>
      intro re
      -- Unfold one attempt on the left and one fresh draw on the right; both bind over the same
      -- raw `ids.commit pk sk` draw, so compare the per-draw fire-marginals termwise.
      rw [run_ghostSignDrawBody_succ]
      rw [OracleComp.drawList, bind_assoc, bind_map_left]
      simp only [bind_assoc, pure_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      refine ENNReal.tsum_le_tsum fun ws => ?_
      gcongr
      -- Per commit draw `ws`: name the recursive fresh `n`-draw game and the recursive body-`n`
      -- game; the latter is `≤` the former by the inductive hypothesis (`ih`).
      set RHSinner : ℝ≥0∞ := Pr[(fun b : Bool => b = true) |
        OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun rest =>
          pure (OracleComp.readManyList rest q σ)] with hRHSinner
      by_cases hhead : OracleComp.readMany ws.1 q σ = true
      · -- The head already fires: the RHS `readManyList (ws.1 :: rest)` is always `true`, so the
        -- RHS per-draw marginal is the full mass of `drawList n` = 1 ≥ the LHS.
        refine le_trans probEvent_le_one (le_of_eq ?_)
        symm
        have hcongr : (OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun rest =>
              pure (OracleComp.readManyList (ws.1 :: rest) q σ))
            = (OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun _ =>
              (pure true : ProbComp Bool)) := by
          refine bind_congr fun rest => ?_
          rw [OracleComp.readManyList, List.any_cons, hhead, Bool.true_or]
        rw [hcongr, probEvent_bind_eq_tsum]
        simp only [probEvent_pure, if_pos]
        rw [ENNReal.tsum_mul_right, OracleComp.tsum_probOutput_drawList_eq_one, one_mul]
      · -- The head misses: the RHS reduces to the recursive fresh game `RHSinner`, and the LHS is
        -- dominated by the recursive body-`n` game, which is `≤ RHSinner` by `ih`.
        rw [Bool.not_eq_true] at hhead
        have hRHS : Pr[(fun b : Bool => b = true) |
              OracleComp.drawList (Prod.fst <$> ids.commit pk sk) n >>= fun rest =>
                pure (OracleComp.readManyList (ws.1 :: rest) q σ)] = RHSinner := by
          rw [hRHSinner]
          refine probEvent_bind_congr fun rest _ => ?_
          rw [OracleComp.readManyList, List.any_cons, hhead, Bool.false_or, OracleComp.readManyList]
        rw [hRHS]
        -- The LHS per-draw game is dominated by the recursive body-`n` game: drop the
        -- `uniformSample`/`respond` draws (mass `≤ 1`); the accept branch records `[]`
        -- (`readManyList [] = false`, fires with probability `0`) and the reject branch's head
        -- test `readMany ws.1 q σ` misses (`hhead`), so its `readManyList (ws.1 :: inner)` reduces
        -- to the body-`n` game's `readManyList inner`.
        refine le_trans ?_ (ih re)
        refine probEvent_bind_le_of_forall_le fun ch _ => ?_
        refine probEvent_bind_le_of_forall_le fun oz _ => ?_
        cases oz with
        | some z => simp [OracleComp.readManyList]
        | none =>
            rw [bind_map_left]
            refine le_of_eq ?_
            refine probEvent_bind_congr fun rws _ => ?_
            rw [OracleComp.readManyList, List.any_cons, hhead, Bool.false_or,
              OracleComp.readManyList]

/-- The deferred-draw handler for the adversary's oracles, driving the distribution-level mono
skeleton against `ghostBlindImpl`. Carries the accumulated drawn-commitment list and a monotone
read-hit flag in place of the eager ghost cache (see `DeferredState`). -/
noncomputable def deferredDrawImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (DeferredState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun cu => (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
        roStep M s.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
        (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1

/-- Tonelli-style rearrangement under a `map`: the expectation of a nonnegative functional under a
mapped computation reindexes along the map. -/
private lemma tsum_probOutput_map_mul' {α β : Type} (oa : ProbComp α)
    (f : α → β) (g : β → ℝ≥0∞) :
    ∑' z, Pr[= z | f <$> oa] * g z = ∑' x, Pr[= x | oa] * g (f x) := by
  rw [map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
  refine tsum_congr fun x => ?_
  simp only [Function.comp_apply]
  rw [tsum_probOutput_pure_mul]

/-- The expectation of a nonnegative functional `F` that is constant (equal to `c`) on the support
of a (sub)probability computation `run` equals `c`. -/
private lemma tsum_probOutput_mul_of_const_on_support {β : Type} (run : ProbComp β) {c : ℝ≥0∞}
    {F : β → ℝ≥0∞} (hconst : ∀ z ∈ support run, F z = c) (hone : Pr[⊥ | run] = 0) :
    ∑' z, Pr[= z | run] * F z = c := by
  have hsum : (∑' z, Pr[= z | run] * F z) = ∑' z, Pr[= z | run] * c := by
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support run
    · rw [hconst z hz]
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
  rw [hsum, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' hone, one_mul]

omit [SampleableType Stmt] in
/-- **Per-step expected drawn-list length growth of the deferred-draw handler.** One step of
`deferredDrawImpl` grows the expected drawn-list length by at most `1/(1-p)` on a signing query and
by `0` on a uniform or random-oracle-read query (which leave the drawn list untouched). The
signing-step bound is the per-query draw count `tsum_probOutput_run_ghostSignDrawBody_mul_length_le`
folded with `geomAttemptSum_le`. This is the per-step charge that the run-level mean fold
`deferredDraw_run_expected_length_le` telescopes against `signHashQueryBound`. -/
lemma deferredDrawImpl_step_expected_length_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredState M Commit Chal,
      Pr[= z | (deferredDrawImpl ids M maxAttempts pk sk t).run s] * (z.2.1.2.length : ℝ≥0∞))
      ≤ (s.1.2.length : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · -- UNIFORM: state untouched, drawn list `s.1.2` preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · -- READ: writes only the base cache / bad flag; drawn list `s.1.2` preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
            roStep M s.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawImpl, StateT.run_mk]
      rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · -- SIGN: drawn list becomes `s.1.2 ++ alc.1.2`; expected new length ≤ 1/(1-p).
    rw [if_pos (by simp)]
    have hrun : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul'
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2)))
      (fun z => (z.2.1.2.length : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              ((s.1.2.length : ℝ≥0∞) + (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append]
          push_cast
          ring
      _ = (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (s.1.2.length : ℝ≥0∞)) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (alc.1.2.length : ℝ≥0∞) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ (s.1.2.length : ℝ≥0∞) + ENNReal.ofReal (1 / (1 - p_abort)) := by
          refine add_le_add ?_ ?_
          · rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          · exact le_trans (tsum_probOutput_run_ghostSignDrawBody_mul_length_le ids M pk sk msg
              hAbort maxAttempts s.1.1.1) (geomAttemptSum_le maxAttempts hp₀ hp)

omit [SampleableType Stmt] in
/-- **Sign-step coupling.** The eager ghost signing body `ghostSignBody` and the deferred draw-
collecting body `ghostSignDrawBody` are coupled, with their `ids.commit`/`uniformSample`/`respond`
draws matched, so that the outputs and real caches agree and the eager ghost layer's key domain is
covered by the front drawn list `drawn` extended with the body's collected commitments. Proved by
induction on the attempt budget: the accept branch writes the accepted commitment to both real
caches and leaves the ghost layer covered by `drawn`; the reject branch records the commitment in
the ghost layer and prepends it to the deferred collected list, recursing with a wider cover. -/
theorem signBody_couple (pk : Stmt) (sk : Wit) (msg : M) :
    ∀ (n : ℕ) (re gh : (M × Commit →ₒ Chal).QueryCache) (drawn : List Commit),
      (∀ mc : M × Commit, gh mc ≠ none → mc.2 ∈ drawn) →
      OracleComp.ProgramLogic.Relational.RelTriple
        ((ghostSignBody ids M pk sk msg n).run (re, gh))
        ((ghostSignDrawBody ids M pk sk msg n).run re)
        (fun p₁ p₂ => p₁.1 = p₂.1.1 ∧ p₁.2.1 = p₂.2 ∧
          (∀ mc : M × Commit, p₁.2.2 mc ≠ none → mc.2 ∈ drawn ++ p₂.1.2))
  | 0, re, gh, drawn, hcov => by
      simp only [ghostSignBody, ghostSignDrawBody, StateT.run_pure]
      exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure
        ⟨rfl, rfl, fun mc hmc => List.mem_append.2 (Or.inl (hcov mc hmc))⟩
  | (n+1), re, gh, drawn, hcov => by
      have hrun₁ : (ghostSignBody ids M pk sk msg (n+1)).run (re, gh) =
          (ids.commit pk sk >>= fun wst => uniformSample Chal >>= fun c =>
            ids.respond pk sk wst.2 c >>= fun oz =>
              match oz with
              | some z => pure (some (wst.1, z),
                  (re.cacheQuery (msg, wst.1) c, uncacheQuery M gh (msg, wst.1)))
              | none => (ghostSignBody ids M pk sk msg n).run
                  (re, gh.cacheQuery (msg, wst.1) c)) := by
        simp only [ghostSignBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
          pure_bind]
        refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
        refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
        refine congrArg (ids.respond pk sk wst.2 c >>= ·) (funext fun oz => ?_)
        cases oz with
        | some z => simp [StateT.run_modify]
        | none => simp [StateT.run_bind, StateT.run_modify]
      have hrun₂ : (ghostSignDrawBody ids M pk sk msg (n+1)).run re =
          (ids.commit pk sk >>= fun wst => uniformSample Chal >>= fun c =>
            ids.respond pk sk wst.2 c >>= fun oz =>
              match oz with
              | some z => pure ((some (wst.1, z), []), re.cacheQuery (msg, wst.1) c)
              | none => (fun rws => ((rws.1.1, wst.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re) := by
        simp only [ghostSignDrawBody, bind_assoc, StateT.run_bind, OracleComp.liftM_run_StateT,
          pure_bind]
        refine congrArg (ids.commit pk sk >>= ·) (funext fun wst => ?_)
        refine congrArg (uniformSample Chal >>= ·) (funext fun c => ?_)
        refine congrArg (ids.respond pk sk wst.2 c >>= ·) (funext fun oz => ?_)
        cases oz with
        | some z => simp [StateT.run_modify]
        | none => simp [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp]
      rw [hrun₁, hrun₂]
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
      rintro wst _ (rfl : wst = _)
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
      rintro c _ (rfl : c = _)
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_
      rintro oz _ (rfl : oz = _)
      cases oz with
      | some z =>
          refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨rfl, rfl, ?_⟩
          intro mc hmc
          -- accept branch: ghost layer is `uncacheQuery M gh (msg, wst.1)`, whose domain ⊆ dom gh
          refine List.mem_append.2 (Or.inl (hcov mc ?_))
          by_cases hmceq : mc = (msg, wst.1)
          · exact absurd (by simp [uncacheQuery, hmceq]) hmc
          · simpa [uncacheQuery, hmceq] using hmc
      | none =>
          have hcov' : ∀ mc : M × Commit, (gh.cacheQuery (msg, wst.1) c) mc ≠ none →
              mc.2 ∈ drawn ++ [wst.1] := by
            intro mc hmc
            by_cases hmceq : mc = (msg, wst.1)
            · subst hmceq; exact List.mem_append.2 (Or.inr (by simp))
            · rw [QueryCache.cacheQuery_of_ne _ _ hmceq] at hmc
              exact List.mem_append.2 (Or.inl (hcov mc hmc))
          have hih := signBody_couple pk sk msg n re (gh.cacheQuery (msg, wst.1) c)
            (drawn ++ [wst.1]) hcov'
          rw [show ((fun rws : (Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache => ((rws.1.1, wst.1 :: rws.1.2), rws.2)) <$>
              (ghostSignDrawBody ids M pk sk msg n).run re)
              = ((ghostSignDrawBody ids M pk sk msg n).run re >>= fun rws =>
                pure ((rws.1.1, wst.1 :: rws.1.2), rws.2)) from by rw [map_eq_bind_pure_comp]; rfl]
          rw [show ((ghostSignBody ids M pk sk msg n).run (re, gh.cacheQuery (msg, wst.1) c))
              = ((ghostSignBody ids M pk sk msg n).run (re, gh.cacheQuery (msg, wst.1) c) >>= pure)
              from by rw [bind_pure]]
          refine OracleComp.ProgramLogic.Relational.relTriple_bind hih ?_
          rintro p₁ p₂ ⟨hout, hcache, hghcov⟩
          refine OracleComp.ProgramLogic.Relational.relTriple_pure_pure ⟨hout, hcache, ?_⟩
          intro mc hmc
          have hmem := hghcov mc hmc
          rw [List.append_assoc] at hmem
          simpa using hmem

/-! ### Stage 3a: the deferred-coupling reduction (Piece A)

The eager ghost-blind bad marginal reduces, through the deferred-draw handler `deferredDrawImpl`,
to the deferred run's bad marginal:

* **Piece A** (`ghostBlind_bad_le_deferredDraw`): a *pointwise coupling* of the eager ghost-blind
  run with the deferred-draw run, established on the pointwise mono skeleton
  `relTriple_simulateQ_run_mono` carrying the state invariant `deferredCoupleInv` (real cache and
  signed list equal; ghost domain covered by the drawn-commitment list; bad-flag ordered). The
  read step is an output-equal coupling (both answer from the real layer via `roStep`, and the
  membership flag fires more readily on the deferred side because it ignores the message component);
  the sign step couples the two bodies' `ids.commit` draws so the eager ghost writes and the
  deferred draws stay in lockstep. `probEvent_le_of_relTriple_imp` then reads off the ordered bad
  marginals.

The deferred run's bad marginal is then carried — through the read-recording reduction
(`deferredDraw_bad_le_readRecord`) and the first-moment Markov step
(`readRecord_pred_le_expected_coincidences`) — to the expected coincidence count bounded by
`readRecord_expected_coincidences_le`.

This reduction uses the pointwise coupling because the bad flags *are* pointwise linkable (eager
ghost-membership ⟹ deferred commitment-membership, since the drawn list grows in lockstep with the
ghost cache), so the pointwise `relTriple_simulateQ_run_mono` route applies and Piece A is genuine,
bankable coupling content. The remaining open content is the value-free fold-lift isolated in
`readRecord_expected_coincidences_le`.

The state invariant linking the eager `GhostState` and the deferred `DeferredState`: real cache and
signed-message list agree, every key in the ghost cache has its commitment recorded in the drawn
list, and the bad flag is ordered (eager-bad ⟹ deferred-bad). The read points coincide because both
sides answer from the (shared) real layer. -/
omit [SampleableType Stmt] in
/-- The coupling invariant between the eager ghost-blind state and the deferred-draw state: real
cache and signed list agree, every ghost-cache key's commitment is in the drawn list, and the bad
flag is ordered. -/
def deferredCoupleInv
    (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal) : Prop :=
  s₁.1.1.1 = s₂.1.1.1 ∧ s₁.1.2 = s₂.1.1.2 ∧
    (∀ mc : M × Commit, s₁.1.1.2 mc ≠ none → mc.2 ∈ s₂.1.2) ∧
    (s₁.2 = true → s₂.2 = true)

omit [SampleableType Stmt] in
/-- **Per-query coupling step for the ghost-blind → deferred coupling.** From any pair of
`deferredCoupleInv`-related states, one step of the eager ghost-blind handler couples with one step
of the deferred-draw handler with equal output and the invariant preserved.

* **Uniform** steps forward the same draw; the state is untouched, so the invariant is inherited.
* **Read** steps answer from the shared real layer via `roStep` (same answer, same cache update);
  the eager bad flag fires on ghost-domain membership and the deferred one on drawn-list membership;
  the domain-coverage invariant makes the eager fire imply the deferred fire (it ignores the message
  component), preserving the bad ordering.
* **Sign** steps invoke `signBody_couple`: the matched `ids.commit` draws keep the outputs and real
  caches equal and extend the drawn list to cover the new ghost writes; the bad flag is intact. -/
theorem deferredCouple_step (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (u₁ : GhostState M Commit Chal) (u₂ : DeferredState M Commit Chal)
    (hu : deferredCoupleInv M u₁ u₂) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((ghostBlindImpl ids M maxAttempts pk sk t).run u₁)
      ((deferredDrawImpl ids M maxAttempts pk sk t).run u₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ deferredCoupleInv M p₁.2 p₂.2) := by
  obtain ⟨hre, hl, hdom, hbad⟩ := hu
  rcases t with (n | mc) | msg
  · -- UNIFORM: both forward the same draw; state untouched.
    have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₁ =
        (fun u => (u, u₁)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₂ =
        (fun u => (u, u₂)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    rw [hrun₁, hrun₂]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    exact ⟨rfl, hre, hl, hdom, hbad⟩
  · -- READ: answer from the shared real layer; bad flag dominated under domain coverage.
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₂ =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, u₂.1.1.2), u₂.1.2), u₂.2 || decide (mc.2 ∈ u₂.1.2)))) <$>
          roStep M u₂.1.1.1 mc := rfl
    cases hgh : u₁.1.1.2 mc with
    | none =>
        have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), u₁.2))) <$> roStep M u₁.1.1.1 mc := by
          rw [ghostBlindImpl_eq_ghostHybridImpl_false]
          exact ghostHybridImpl_run_ro_ghost_none ids M maxAttempts false pk sk hgh
        rw [hrun₁, hrun₂, hre]
        refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
          (OracleComp.ProgramLogic.Relational.relTriple_post_mono
            (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
        rintro a b (rfl : a = b)
        exact ⟨rfl, rfl, hl, hdom, fun hb => by rw [hbad hb]; rfl⟩
    | some v =>
        have hgh2 : u₁.1.1.2 mc ≠ none := by rw [hgh]; exact Option.some_ne_none v
        have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), true))) <$> roStep M u₁.1.1.1 mc := by
          rw [ghostBlindImpl_eq_ghostHybridImpl_false,
            ghostHybridImpl_run_ro_ghost_some ids M maxAttempts false pk sk hgh,
            if_neg Bool.false_ne_true]
        rw [hrun₁, hrun₂, hre]
        refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
          (OracleComp.ProgramLogic.Relational.relTriple_post_mono
            (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
        rintro a b (rfl : a = b)
        have hdef : (u₂.2 || decide (mc.2 ∈ u₂.1.2)) = true := by simp [hdom mc hgh2]
        exact ⟨rfl, rfl, hl, hdom, fun _ => hdef⟩
  · -- SIGN: couple the two signing bodies via `signBody_couple`; bad flag untouched.
    have hrun₁ : (ghostBlindImpl ids M maxAttempts pk sk (.inr msg)).run u₁ =
        (fun alc : Option (Commit × Resp) ×
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) =>
          (alc.1, ((alc.2, msg :: u₁.1.2), u₁.2))) <$>
          (ghostSignBody ids M pk sk msg maxAttempts).run u₁.1.1 := by
      rw [ghostBlindImpl_eq_ghostHybridImpl_false]
      exact ghostHybridImpl_run_sign ids M maxAttempts false pk sk msg u₁
    have hrun₂ : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run u₂ =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: u₂.1.1.2), u₂.1.2 ++ alc.1.2), u₂.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run u₂.1.1.1 := rfl
    rw [hrun₁, hrun₂]
    have hu11 : u₁.1.1 = (u₂.1.1.1, u₁.1.1.2) := by rw [← hre]
    rw [hu11]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (signBody_couple ids M pk sk msg maxAttempts u₂.1.1.1 u₁.1.1.2 u₂.1.2 hdom) ?_)
    rintro p₁ p₂ ⟨hout, hcache, hghcov⟩
    exact ⟨hout, hcache, by rw [hl], hghcov, hbad⟩

omit [SampleableType Stmt] in
/-- **The ghost-blind → deferred run coupling.** By induction on the adversary computation `oa`,
the eager ghost-blind run and the deferred-draw run are coupled with the invariant
`deferredCoupleInv` preserved at every leaf, using `deferredCouple_step` at each query and the
inductive hypothesis for the continuation. -/
theorem deferredCouple_run {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal),
      deferredCoupleInv M s₁ s₂ →
      OracleComp.ProgramLogic.Relational.RelTriple
        ((simulateQ (ghostBlindImpl ids M maxAttempts pk sk) oa).run s₁)
        ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₂)
        (fun q₁ q₂ => deferredCoupleInv M q₁.2 q₂.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s₁ s₂ hinv
      simp only [simulateQ_pure, StateT.run_pure]
      exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure hinv
  | query_bind t ob ih =>
      intro s₁ s₂ hinv
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (deferredCouple_step ids M maxAttempts pk sk t s₁ s₂ hinv) ?_
      rintro p₁ p₂ ⟨hout, hinv'⟩
      rw [show p₁.1 = p₂.1 from hout]
      exact ih p₂.1 p₁.2 p₂.2 hinv'

omit [SampleableType Stmt] in
/-- **Piece A: the ghost-blind → deferred coupling.** The ghost-blind run's bad marginal is at most
the deferred-draw run's bad marginal, from any pair of `deferredCoupleInv`-related start states.

Reads off the bad-flag ordering component of the invariant from the run coupling
`deferredCouple_run` via `probEvent_le_of_relTriple_imp`. -/
theorem ghostBlind_bad_le_deferredDraw {γ : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s₁ : GhostState M Commit Chal) (s₂ : DeferredState M Commit Chal)
    (hinv : deferredCoupleInv M s₁ s₂) :
    Pr[fun z : γ × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) oa).run s₁]
      ≤ Pr[fun z : γ × DeferredState M Commit Chal => z.2.2 = true |
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₂] :=
  OracleComp.ProgramLogic.Relational.probEvent_le_of_relTriple_imp
    (deferredCouple_run ids M maxAttempts pk sk oa s₁ s₂ hinv)
    (fun _ _ hp => hp.2.2.2)

omit [SampleableType Stmt] in
/-- **The drawn list only grows.** Every reachable final state of the deferred-draw run from a
start state `s` has the start's drawn list `s.1.2` as a prefix: uniform and read steps leave the
drawn list untouched, and a signing step appends (`s.1.2 ++ alc.1.2`). Hence the number of *new*
draws is `final.length - s.1.2.length` and is well-behaved (`s.1.2.length ≤ final.length`). -/
theorem deferredDraw_run_drawn_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredState M Commit Chal)
      (z : γ × DeferredState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.2 <+: z.2.1.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact List.prefix_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine List.IsPrefix.trans ?_ (ih x.1 x.2 z hzx)
      -- The step's output drawn list extends `s.1.2`.
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact List.prefix_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
              roStep M s.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact List.prefix_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; exact List.prefix_append s.1.2 alc.1.2

omit [SampleableType Stmt] in
/-- **The signed-message list only grows in length.** Every reachable final state of the
deferred-draw run from a start state `s` has signed-message list at least as long as the start's
`s.1.1.2`: uniform and read steps leave it untouched, and a signing step prepends one message
(`msg :: s.1.1.2`). Hence the number of *new* signing queries is `final.length - s.1.1.2.length`. -/
theorem deferredDraw_run_signed_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredState M Commit Chal)
      (z : γ × DeferredState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.1.2.length ≤ z.2.1.1.2.length := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine le_trans ?_ (ih x.1 x.2 z hzx)
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
              roStep M s.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; simp

omit [SampleableType Stmt] in
/-- **Run-level expected drawn-list length of the deferred-draw run.** By induction on the
adversary computation `oa`, the expected final drawn-list length of the deferred-draw run from a
start state `s` is at most `s.1.2.length + qSrem · (1/(1-p))`, where `qSrem` bounds the number of
signing queries `oa` makes (the `(· matches .inr _)` component of `signHashQueryBound`). Each
signing query grows the expected drawn length by at most `1/(1-p)` (the per-step charge
`deferredDrawImpl_step_expected_length_le`), and uniform/read queries leave it unchanged; the
signing-query budget `qSrem` telescopes across the fold exactly as in
`IsQueryBoundP.simulateQ_run_StateT_of_step`. This is the mean bound that the constructed count law
`kn` of Piece B inherits. -/
theorem deferredDraw_run_expected_length_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredState M Commit Chal),
        (∑' z : γ × DeferredState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s] *
            (z.2.1.2.length : ℝ≥0∞))
          ≤ (s.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      -- Total mass of one deferred step is `1` (no failure).
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
          Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawImpl]
          · simp only [deferredDrawImpl, StateT.run_mk]
            rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawImpl])
      -- Abstract the continuation's carried budget `b` and the per-step abort charge.
      -- Generic combiner: with continuation bound `≤ x.length + b·c`, step charge `extra`,
      -- and `extra + b·c ≤ qSrem·c`, the fold gives the run bound.
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
            (∑' z : γ × DeferredState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                (z.2.1.2.length : ℝ≥0∞))
              ≤ (x.2.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
            (x.2.1.2.length : ℝ≥0∞)) ≤ (s.1.2.length : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                  (z.2.1.2.length : ℝ≥0∞))
            ≤ (s.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * (z.2.1.2.length : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                ((x.2.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                  (x.2.1.2.length : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                    ((x.2.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      (x.2.1.2.length : ℝ≥0∞) +
                    Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ ((s.1.2.length : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by gcongr
          _ ≤ (s.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by rw [add_assoc]; gcongr
      -- Case on the query head so the `if p t` budget/charge reduce concretely.
      rcases t with (n | mc) | msg
      · -- UNIFORM: budget unchanged, no charge.
        refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · -- READ: budget unchanged, no charge.
        refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · -- SIGN: budget decrements; `0 < qSrem`, charge `c`, recombine `c + (qSrem-1)·c = qSrem·c`.
        have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawImpl_step_expected_length_le ids M maxAttempts pk sk
            hp₀ hp hAbort (.inr msg) s
          rwa [if_pos (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **The deferred-draw run never fails.** Every step of `deferredDrawImpl` is a pushforward of a
non-failing `ProbComp` (uniform sampling, `roStep`, or the draw-collecting signing body), so the
whole `simulateQ` fold has zero failure mass. -/
theorem deferredDraw_run_neverFail {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredState M Commit Chal),
      Pr[⊥ | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s] = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; simp [simulateQ_pure]
  | query_bind t ob ih =>
      intro s
      rw [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff]
      refine ⟨?_, fun x _ => ih x.1 x.2⟩
      rcases t with (n | mc) | msg
      · simp [deferredDrawImpl]
      · simp only [deferredDrawImpl]
        rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
      · simp [deferredDrawImpl]

omit [SampleableType Stmt] in
/-- **The constructed count law of Piece B and its mean bound.** Mapping the deferred-draw run to
its number of *new* draws beyond the start prefix `ws₀` (i.e. `final.length - ws₀.length`) gives a
count law `kn` whose mean is at most `qSrem/(1-p)`. The mean equals the expected total drawn length
minus `ws₀.length` (valid because `ws₀` is always a prefix, `deferredDraw_run_drawn_prefix`), and
the expected total length is bounded by `ws₀.length + qSrem·(1/(1-p))`
(`deferredDraw_run_expected_length_le`), so the `ws₀.length` cancels. This is the mean obligation of
Piece B, discharged for the constructed `kn`. -/
theorem deferredDraw_kn_mean_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ) (hQ : oa.IsQueryBoundP (· matches Sum.inr _) qSrem)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) (ws₀ : List Commit) :
    (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal => z.2.1.2.length - ws₀.length) <$>
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false)] *
        (n : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) / (1 - p_abort)) := by
  classical
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set run : ProbComp (γ × DeferredState M Commit Chal) :=
    (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false) with hrun
  -- The mean of `kn` equals the run-expectation of the new-draw count.
  have hmean : (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal => z.2.1.2.length - ws₀.length) <$> run] *
        (n : ℝ≥0∞))
      = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
          ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞) :=
    tsum_probOutput_map_mul' run
      (fun z => z.2.1.2.length - ws₀.length) (fun n => (n : ℝ≥0∞))
  rw [hmean]
  -- Add back `ws₀.length` to recover the total-length expectation, bounded by the fold lemma.
  have hsplit : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞)) + (ws₀.length : ℝ≥0∞)
      ≤ (ws₀.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    have hmass : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run]) = 1 := by
      rw [hrun]
      exact tsum_probOutput_eq_one'
        (deferredDraw_run_neverFail ids M maxAttempts pk sk oa (((re, l), ws₀), false))
    calc (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞)) + (ws₀.length : ℝ≥0∞)
        = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            (((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞) + (ws₀.length : ℝ≥0∞)) := by
          rw [show (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                (((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞) + (ws₀.length : ℝ≥0∞)))
              = (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                  ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞)) +
                ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] * (ws₀.length : ℝ≥0∞) from by
              rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
          rw [ENNReal.tsum_mul_right, hmass, one_mul]
      _ = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            (z.2.1.2.length : ℝ≥0∞) := by
          refine tsum_congr fun z => ?_
          by_cases hz : z ∈ support run
          · have hpre : ws₀.length ≤ z.2.1.2.length :=
              (deferredDraw_run_drawn_prefix ids M maxAttempts pk sk oa _ z hz).length_le
            congr 1
            rw [← Nat.cast_add, Nat.sub_add_cancel hpre]
          · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
      _ ≤ (ws₀.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
          have := deferredDraw_run_expected_length_le ids M maxAttempts pk sk hp₀ hp hAbort oa
            qSrem hQ (((re, l), ws₀), false)
          rwa [← hrun] at this
  -- Cancel `ws₀.length` (finite) and rewrite `qSrem·ofReal(1/(1-p)) = ofReal(qSrem/(1-p))`.
  have hcancel : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        ((z.2.1.2.length - ws₀.length : ℕ) : ℝ≥0∞))
      ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [add_comm] at hsplit
    exact (ENNReal.add_le_add_iff_left (by simp : (ws₀.length : ℝ≥0∞) ≠ ∞)).mp hsplit
  refine hcancel.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_natCast qSrem, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### Attempt-count law: the tight redraft of the deferral count

The firing event tests reads against the *actual* (rejected) drawn list, whose draws are skewed by
the rejection conditioning `commit | reject`. The `drawList`-game RHS, by contrast, draws *raw*
`Prod.fst <$> ids.commit pk sk`. A reject-count `kn = drawnlist.length` is therefore *too small* to
dominate the firing (the residual was false-as-stated with that `kn`). The sound count is the total
*attempt* count, which over-counts each query's rejected draws by the accepting attempt's one fresh
raw draw and whose mean is exactly `qSrem/(1-p)`.

The attempt count is recovered *without a new state field* as `(drawn-list growth) + (signed-list
growth)`: every signing query increments the signed-message list by exactly one (in
`deferredDrawImpl`'s sign branch) and the drawn list by its rejected-attempt count. Their sum
dominates the per-query attempt count and has the clean charge `∑_{a≤maxAttempts} p^a ≤ 1/(1-p)`,
combining the tight reject bound (`tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight`, the
`∑_{a<n} p^(a+1)` rejects) with the unconditional `+1` (signed list). -/

omit [SampleableType Stmt] in
/-- **Per-step expected attempt-count growth of the deferred-draw handler.** One step of
`deferredDrawImpl` grows the expected combined size `drawnlist.length + signedlist.length` by at
most `1/(1-p)` on a signing query and by `0` on uniform/read queries. On a signing query the drawn
list grows by the rejected-attempt count (expected `≤ ∑_{a<maxAttempts} p^(a+1)`, the tight bound)
and the signed list grows by exactly `1`; their sum is `∑_{a≤maxAttempts} p^a ≤ 1/(1-p)`. This is
the per-step charge for the attempt-count law `kn`. -/
lemma deferredDrawImpl_step_expected_attemptCount_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredState M Commit Chal,
      Pr[= z | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
        ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
      ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · -- UNIFORM: state untouched.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · -- READ: writes only the base cache / bad flag; both lists preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, s.1.1.2), s.1.2), s.2 || decide (mc.2 ∈ s.1.2)))) <$>
            roStep M s.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawImpl, StateT.run_mk]
      rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · -- SIGN: drawn list `s.1.2 ++ alc.1.2`, signed list `msg :: s.1.1.2` (one longer).
    rw [if_pos (by simp)]
    have hrun : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul'
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, (((alc.2, msg :: s.1.1.2), s.1.2 ++ alc.1.2), s.2)))
      (fun z => ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞) +
                (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append, List.length_cons]
          push_cast
          ring
      _ = ((∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞))) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1] *
              (alc.1.2.length : ℝ≥0∞)) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + ENNReal.ofReal (1 / (1 - p_abort)) := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          rw [add_assoc]
          gcongr
          refine le_trans (add_le_add_right
            (tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight ids M pk sk msg
              hAbort maxAttempts s.1.1.1) _) ?_
          rw [add_comm]
          refine le_trans (le_of_eq ?_) (geomSum_le hp₀ hp (maxAttempts + 1))
          rw [Finset.sum_range_succ']
          simp only [pow_zero]

omit [SampleableType Stmt] in
/-- **Run-level expected attempt count of the deferred-draw run.** By induction on `oa`, the
expected combined size `drawnlist.length + signedlist.length` of the deferred-draw run from a start
state `s` is at most `(s.1.2.length + s.1.1.2.length) + qSrem · (1/(1-p))`, where `qSrem` bounds the
number of signing queries. Each signing query grows the expected combined size by at most `1/(1-p)`
(the per-step charge `deferredDrawImpl_step_expected_attemptCount_le`), and uniform/read queries
leave it unchanged; the signing-query budget telescopes across the fold exactly as in
`deferredDraw_run_expected_length_le`. The attempt-count law `kn` of the redrafted residual inherits
this mean. -/
theorem deferredDraw_run_expected_attemptCount_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredState M Commit Chal),
        (∑' z : γ × DeferredState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s] *
            ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
          ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) +
              (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
          Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawImpl]
          · simp only [deferredDrawImpl, StateT.run_mk]
            rcases hg : s.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawImpl])
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredState M Commit Chal,
            (∑' z : γ × DeferredState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
            ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                  ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                (((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                  ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                    (((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      ((x.2.1.2.length + x.2.1.1.2.length : ℕ) : ℝ≥0∞) +
                    Pr[= x | (deferredDrawImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ (((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by gcongr
          _ ≤ ((s.1.2.length + s.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
              rw [add_assoc]; gcongr
      rcases t with (n | mc) | msg
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
            hp₀ hp hAbort (.inr msg) s
          rwa [if_pos (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **The attempt-count law of the redrafted residual and its mean bound.** Mapping the
deferred-draw run to its attempt count — the combined new growth of the drawn and signed lists,
`(drawnlist.length - ws₀.length) + (signedlist.length - l.length)` — gives a count law whose mean is
at most `qSrem/(1-p)`. The attempt count dominates the reject count (it adds the signed-list growth,
one per signing query, covering each accepting attempt's fresh raw draw) yet keeps the same clean
mean, because the per-query charge `(reject expectation) + 1 = ∑_{a≤maxAttempts} p^a ≤ 1/(1-p)` is
identical to the loose reject charge — the `+1` is absorbed by tightening the reject bound from
`∑_{a<n} p^a` to `∑_{a<n} p^(a+1)`. -/
theorem deferredDraw_attemptKn_mean_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ) (hQ : oa.IsQueryBoundP (· matches Sum.inr _) qSrem)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) (ws₀ : List Commit) :
    (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal =>
            (z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length)) <$>
          (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false)] *
        (n : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) / (1 - p_abort)) := by
  classical
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set run : ProbComp (γ × DeferredState M Commit Chal) :=
    (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run (((re, l), ws₀), false) with hrun
  have hmean : (∑' n : ℕ, Pr[= n |
        (fun z : γ × DeferredState M Commit Chal =>
            (z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length)) <$> run] *
        (n : ℝ≥0∞))
      = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
          (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) :=
    tsum_probOutput_map_mul' run
      (fun z => (z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length))
      (fun n => (n : ℝ≥0∞))
  rw [hmean]
  -- Add back `ws₀.length + l.length` to recover the total combined size, bounded by the fold.
  have hmass : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run]) = 1 := by
    rw [hrun]
    exact tsum_probOutput_eq_one'
      (deferredDraw_run_neverFail ids M maxAttempts pk sk oa (((re, l), ws₀), false))
  have hsplit : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
        ((ws₀.length + l.length : ℕ) : ℝ≥0∞)
      ≤ ((ws₀.length + l.length : ℕ) : ℝ≥0∞) +
          (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    calc (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
          ((ws₀.length + l.length : ℕ) : ℝ≥0∞)
        = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            ((((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) +
              ((ws₀.length + l.length : ℕ) : ℝ≥0∞)) := by
          rw [show (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                ((((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) +
                  ((ws₀.length + l.length : ℕ) : ℝ≥0∞)))
              = (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                  (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
                ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
                  ((ws₀.length + l.length : ℕ) : ℝ≥0∞) from by
              rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
          rw [ENNReal.tsum_mul_right, hmass, one_mul]
      _ = ∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
            ((z.2.1.2.length + z.2.1.1.2.length : ℕ) : ℝ≥0∞) := by
          refine tsum_congr fun z => ?_
          by_cases hz : z ∈ support run
          · have hpre : ws₀.length ≤ z.2.1.2.length :=
              (deferredDraw_run_drawn_prefix ids M maxAttempts pk sk oa _ z hz).length_le
            have hpre2 : l.length ≤ z.2.1.1.2.length :=
              deferredDraw_run_signed_prefix ids M maxAttempts pk sk oa _ z hz
            congr 1
            rw [← Nat.cast_add]
            congr 1
            omega
          · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
      _ ≤ ((ws₀.length + l.length : ℕ) : ℝ≥0∞) +
            (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
          have := deferredDraw_run_expected_attemptCount_le ids M maxAttempts pk sk hp₀ hp hAbort
            oa qSrem hQ (((re, l), ws₀), false)
          rwa [← hrun] at this
  have hcancel : (∑' z : γ × DeferredState M Commit Chal, Pr[= z | run] *
        (((z.2.1.2.length - ws₀.length) + (z.2.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
      ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [add_comm] at hsplit
    exact (ENNReal.add_le_add_iff_left (by simp : ((ws₀.length + l.length : ℕ) : ℝ≥0∞) ≠ ∞)).mp
      hsplit
  refine hcancel.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_natCast qSrem, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-! ### Read-recording handler: bad as a final-state predicate

The deferred-draw run's bad flag is set at *read time*: a read fires when its target commitment is
in the drawn list **as it stands at that read**. Because the drawn list only grows
(`deferredDraw_run_drawn_prefix`), a read that hits the drawn-so-far list certainly hits the *final*
drawn list, so the bad event is dominated by the final-state predicate "some recorded read-commit
is in the final drawn list". The handler `deferredDrawReadImpl` records, in an extra `List Commit`
component, the commitment `mc.2` of every adversarial read; its read step is otherwise identical to
`deferredDrawImpl` (same answer via `roStep`, same drawn list, same bad flag). The reduction
`deferredDraw_bad_le_readRecord` is the Piece A-style pointwise coupling that reads the bad ordering
off the run; it converts the *read-time* bad flag into the *final-state* membership predicate
`∃ rc ∈ readlist, rc ∈ drawnlist`, which removes the read-time/final-state mismatch that obstructs a
direct expectation bound (see the residual docstring). The recorded read commits are **value-free**
(answers come from the real layer via `roStep`; the drawn *values* never feed the read points), the
content reused by the remaining deferral commute. -/

/-- State of the read-recording deferred-draw handler: the underlying `DeferredState` together with
the accumulated list of commitment components `mc.2` of every adversarial random-oracle read. The
extra list makes the read-hit event a *final-state* predicate (membership in the drawn list) rather
than a read-time flag. -/
abbrev DeferredReadState (M Commit Chal : Type) : Type :=
  DeferredState M Commit Chal × List Commit

/-- The read-recording deferred-draw handler. Identical to `deferredDrawImpl` on the underlying
`DeferredState`, additionally appending the read's commitment component `mc.2` to the recorded
read-commit list on every adversarial random-oracle read. Uniform and signing steps leave the
read-commit list untouched. -/
noncomputable def deferredDrawReadImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (DeferredReadState M Commit Chal) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun cu => (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
          mc.2 :: s.2))) <$>
        roStep M s.1.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
        (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1

omit [SampleableType Stmt] in
/-- **Coupling invariant for the read-recording reduction.** The underlying deferred state matches,
and whenever the deferred bad flag is set there is a recorded read-commit already in the deferred
drawn list. The drawn list grows monotonically, so a read-time hit (recorded in the bad flag) is
witnessed by a recorded read-commit lying in the *current* (hence final) drawn list. -/
def deferredReadInv
    (s₁ : DeferredState M Commit Chal) (s₂ : DeferredReadState M Commit Chal) : Prop :=
  s₁.1 = s₂.1.1 ∧ (s₁.2 = true → ∃ rc ∈ s₂.2, rc ∈ s₂.1.1.2)

omit [SampleableType Stmt] in
/-- **Per-query coupling step for the read-recording reduction.** From any pair of
`deferredReadInv`-related states one step of `deferredDrawImpl` couples with one step of
`deferredDrawReadImpl` with equal output and the invariant preserved.

* **Uniform** forwards the same draw; states untouched.
* **Read** answers from the shared real layer via `roStep` (same answer, same cache, same drawn
  list); the recorded read-commit `mc.2` witnesses any newly-set bad flag (it is appended to the
  read-commit list and, when the flag fires, lies in the drawn list).
* **Sign** runs the shared `ghostSignDrawBody`; the drawn list grows in lockstep, so an existing
  read-commit witness is preserved (the drawn list only appends). -/
theorem deferredDrawRead_step (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (u₁ : DeferredState M Commit Chal) (u₂ : DeferredReadState M Commit Chal)
    (hu : deferredReadInv M u₁ u₂) :
    OracleComp.ProgramLogic.Relational.RelTriple
      ((deferredDrawImpl ids M maxAttempts pk sk t).run u₁)
      ((deferredDrawReadImpl ids M maxAttempts pk sk t).run u₂)
      (fun p₁ p₂ => p₁.1 = p₂.1 ∧ deferredReadInv M p₁.2 p₂.2) := by
  obtain ⟨hst, hbad⟩ := hu
  rcases t with (n | mc) | msg
  · -- UNIFORM: both forward the same draw; state untouched.
    have hrun₁ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₁ =
        (fun u => (u, u₁)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    have hrun₂ : (deferredDrawReadImpl ids M maxAttempts pk sk (.inl (.inl n))).run u₂ =
        (fun u => (u, u₂)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
    rw [hrun₁, hrun₂]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    exact ⟨rfl, hst, hbad⟩
  · -- READ: shared `roStep`; the recorded read-commit witnesses any newly-set bad flag.
    have hrun₁ : (deferredDrawImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₁ =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, (((cu.2, u₁.1.1.2), u₁.1.2), u₁.2 || decide (mc.2 ∈ u₁.1.2)))) <$>
          roStep M u₁.1.1.1 mc := rfl
    have hrun₂ : (deferredDrawReadImpl ids M maxAttempts pk sk (.inl (.inr mc))).run u₂ =
        (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, ((((cu.2, u₂.1.1.1.2), u₂.1.1.2), u₂.1.2 || decide (mc.2 ∈ u₂.1.1.2)),
              mc.2 :: u₂.2))) <$>
          roStep M u₂.1.1.1.1 mc := rfl
    rw [hrun₁, hrun₂, show u₁.1.1.1 = u₂.1.1.1.1 from by rw [hst],
      show u₁.1.1.2 = u₂.1.1.1.2 from by rw [hst], show u₁.1.2 = u₂.1.1.2 from by rw [hst]]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    refine ⟨rfl, rfl, ?_⟩
    intro hb
    rcases Bool.or_eq_true _ _ |>.mp hb with hb' | hb'
    · obtain ⟨rc, hrcmem, hrcdraw⟩ := hbad hb'
      exact ⟨rc, List.mem_cons_of_mem _ hrcmem, hrcdraw⟩
    · exact ⟨mc.2, List.mem_cons_self, by simpa using hb'⟩
  · -- SIGN: shared signing body; drawn list grows, witness preserved.
    have hrun₁ : (deferredDrawImpl ids M maxAttempts pk sk (.inr msg)).run u₁ =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, (((alc.2, msg :: u₁.1.1.2), u₁.1.2 ++ alc.1.2), u₁.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run u₁.1.1.1 := rfl
    have hrun₂ : (deferredDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run u₂ =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, ((((alc.2, msg :: u₂.1.1.1.2), u₂.1.1.2 ++ alc.1.2), u₂.1.2), u₂.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run u₂.1.1.1.1 := rfl
    rw [hrun₁, hrun₂, show u₁.1.1.1 = u₂.1.1.1.1 from by rw [hst],
      show u₁.1.1.2 = u₂.1.1.1.2 from by rw [hst], show u₁.1.2 = u₂.1.1.2 from by rw [hst]]
    refine OracleComp.ProgramLogic.Relational.relTriple_map (R := _)
      (OracleComp.ProgramLogic.Relational.relTriple_post_mono
        (OracleComp.ProgramLogic.Relational.relTriple_refl _) ?_)
    rintro a b (rfl : a = b)
    refine ⟨rfl, rfl, ?_⟩
    intro hb
    obtain ⟨rc, hrcmem, hrcdraw⟩ := hbad hb
    exact ⟨rc, hrcmem, List.mem_append_left _ hrcdraw⟩

omit [SampleableType Stmt] in
/-- **The read-recording run coupling.** By induction on the adversary computation `oa`, the
deferred-draw run and the read-recording run are coupled with `deferredReadInv` preserved at every
leaf, using `deferredDrawRead_step` per query and the inductive hypothesis for the continuation.
Mirrors `deferredCouple_run`. -/
theorem deferredDrawRead_run {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s₁ : DeferredState M Commit Chal) (s₂ : DeferredReadState M Commit Chal),
      deferredReadInv M s₁ s₂ →
      OracleComp.ProgramLogic.Relational.RelTriple
        ((simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₁)
        ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s₂)
        (fun q₁ q₂ => deferredReadInv M q₁.2 q₂.2) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s₁ s₂ hinv
      simp only [simulateQ_pure, StateT.run_pure]
      exact OracleComp.ProgramLogic.Relational.relTriple_pure_pure hinv
  | query_bind t ob ih =>
      intro s₁ s₂ hinv
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      refine OracleComp.ProgramLogic.Relational.relTriple_bind
        (deferredDrawRead_step ids M maxAttempts pk sk t s₁ s₂ hinv) ?_
      rintro p₁ p₂ ⟨hout, hinv'⟩
      rw [show p₁.1 = p₂.1 from hout]
      exact ih p₂.1 p₁.2 p₂.2 hinv'

omit [SampleableType Stmt] in
/-- **The read-recording reduction.** The deferred-draw run's bad marginal is at most the
read-recording run's final-state predicate "some recorded read-commit lies in the final drawn
list", from any pair of `deferredReadInv`-related start states.

Reads off the bad-ordering component of `deferredReadInv` from the run coupling
`deferredDrawRead_run` via `probEvent_le_of_relTriple_imp`. This converts the read-time bad flag of
`deferredDrawImpl` into the membership predicate over the read-recording run's final state, where
both the recorded read-commit list and the drawn list are available together. -/
theorem deferredDraw_bad_le_readRecord {γ : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s₁ : DeferredState M Commit Chal) (s₂ : DeferredReadState M Commit Chal)
    (hinv : deferredReadInv M s₁ s₂) :
    Pr[fun z : γ × DeferredState M Commit Chal => z.2.2 = true |
        (simulateQ (deferredDrawImpl ids M maxAttempts pk sk) oa).run s₁]
      ≤ Pr[fun z : γ × DeferredReadState M Commit Chal => ∃ rc ∈ z.2.2, rc ∈ z.2.1.1.2 |
          (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s₂] :=
  OracleComp.ProgramLogic.Relational.probEvent_le_of_relTriple_imp
    (deferredDrawRead_run ids M maxAttempts pk sk oa s₁ s₂ hinv)
    (fun _ _ hp hbad => hp.2 hbad)

omit [SampleableType Stmt] in
/-- **Markov reduction for the read-recording firing event.** The read-recording run's final-state
read-hit predicate `∃ rc ∈ readlist, rc ∈ drawnlist` has probability at most the *expected
coincidence count* `E[#{ rc ∈ readlist : rc ∈ drawnlist }]`, the first moment of the number of
recorded read-commits that lie in the drawn list.

This is the elementary first-moment (Markov) step of the per-position route: a firing run has at
least one coincidence, so the indicator of the firing event is dominated by the (nonnegative,
integer-valued) coincidence count, and `Pr[fire] ≤ E[count]` by the Markov core
`probEvent_le_tsum_probOutput_mul_cost`. The remaining content — bounding `E[count]` by
`(qH+1)·ε·E[#attempts]` — is the genuine per-position independence of each fresh draw from the
value-free recorded read-commit list (see `readRecord_expected_coincidences_le`). This lemma is
axiom-clean and isolates that independence as the sole open content. -/
theorem readRecord_pred_le_expected_coincidences {γ : Type}
    (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s : DeferredReadState M Commit Chal) :
    Pr[fun z : γ × DeferredReadState M Commit Chal => ∃ rc ∈ z.2.2, rc ∈ z.2.1.1.2 |
        (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s]
      ≤ ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞) := by
  classical
  refine probEvent_le_tsum_probOutput_mul_cost _ _ _ (fun z hz => ?_)
  obtain ⟨rc, hrc, hrd⟩ := hz
  have hpos : 0 < z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) := by
    rw [List.countP_pos_iff]
    exact ⟨rc, hrc, by simpa using hrd⟩
  have h1 : (1 : ℕ) ≤ z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) := hpos
  exact_mod_cast h1

/-! ### First-moment reduction scaffolding for the coincidence-count bound

The numeric residual `readRecord_expected_coincidences_le` reduces, by elementary arithmetic, to a
single value-free cross-term atom. The reduction chain:

* the coincidence count is dominated by the pair count
  `Σ_{rc ∈ readlist} drawnlist.count rc` (`List.countP_le_sum_count_mem`);
* the *number of recorded reads* is bounded **deterministically** by the read-query budget `qH`
  (`deferredDrawReadImpl_run_readlist_length_le`), so the read-recording run's readlist length is at
  most `s.readlist.length + qH`;
* the expected drawn-list length of the read-recording run is at most
  `s.drawnlist.length + qSrem · (1/(1-p))` (`deferredDrawRead_run_expected_drawnlist_length_le`, the
  read-recording counterpart of `deferredDraw_run_expected_length_le`);
* the genuine content is then the **value-free per-pair atom** `readRecord_expected_pairs_le`:
  the expected pair count is at most `ε` times the expected `readlist.length · drawnlist.length`,
  because each recorded drawn commit is a fresh raw `Prod.fst <$> ids.commit` draw (mass `≤ ε`) and
  is independent of the value-free recorded read-commit list.

`readRecord_expected_coincidences_le` chains these with the deterministic read bound
(`readlist.length ≤ qH+1` from the empty start) and the final-arithmetic conversion. -/

/-- Domination of the membership count by the per-element coincidence count: the number of recorded
read-commits lying in the drawn list is at most `Σ_{rc ∈ readlist} drawnlist.count rc`, the total
number of coinciding `(read, draw)` pairs. -/
private lemma countP_mem_le_sum_count {α : Type} [DecidableEq α] (l d : List α) :
    l.countP (fun rc => decide (rc ∈ d)) ≤ (l.map (fun rc => d.count rc)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons]
      by_cases h : a ∈ d
      · simp only [decide_eq_true_eq, h, if_true]
        have : 1 ≤ d.count a := List.one_le_count_iff.mpr h
        omega
      · simp only [decide_eq_true_eq, h, if_false]
        omega

/-- Expressing a `List.count` as a sum of equality indicators over the list. -/
private lemma count_eq_sum_map_ite {α : Type} [DecidableEq α] (d : List α) (a : α) :
    (d.map (fun w => (if w = a then 1 else 0))).sum = d.count a := by
  induction d with
  | nil => simp
  | cons x d ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.count_cons]
      by_cases h : x = a
      · simp [h]; ring
      · simp [h]

/-- **Symmetric double-count of two lists.** Summing `d.count rc` over `rc ∈ l` equals summing
`l.count w` over `w ∈ d`; both count the coinciding `(read, draw)` pairs
(`Σ_x l.count x · d.count x`). This re-index lets the per-pair charge be organised by the
*draw* list (whose entries are fresh i.i.d. commitments) rather than the read list. -/
private lemma sum_map_count_comm {α : Type} [DecidableEq α] (l d : List α) :
    (l.map (fun rc => d.count rc)).sum = (d.map (fun w => l.count w)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      have key : (d.map (fun w => (a :: l).count w)).sum
          = (d.map (fun w => (if w = a then 1 else 0))).sum + (d.map (fun w => l.count w)).sum := by
        rw [← List.sum_map_add]
        refine congrArg _ (List.map_congr_left fun w _ => ?_)
        rw [List.count_cons]
        by_cases h : w = a
        · subst h; simp [add_comm]
        · simp [h, Ne.symm h]
      rw [key, count_eq_sum_map_ite, add_comm]

omit [SampleableType Stmt] in
/-- **Deterministic readlist-length bound.** Every reachable final state of the read-recording run
records at most `qH` new read-commits, where `qH` bounds the random-oracle (read) queries `oa` makes
(the `(· matches .inl (.inr _))` component of `signHashQueryBound`): each read step prepends exactly
one commitment to the recorded read-commit list and uniform/signing steps leave it untouched. Hence
`readlist.length ≤ s.readlist.length + qH` on the whole support — a *deterministic* (support-wide)
bound, used to dominate the random `readlist.length` factor of the pair count by the constant
`qH`. -/
theorem deferredDrawReadImpl_run_readlist_length_le {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qH : ℕ), oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH →
      ∀ (s : DeferredReadState M Commit Chal)
        (z : γ × DeferredReadState M Commit Chal),
        z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s) →
        z.2.2.length ≤ s.2.length + qH := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qH _ s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; simp
  | query_bind t ob ih =>
      intro qH hQ s z hz
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      rcases t with (n | mc) | msg
      · -- UNIFORM: readlist untouched; budget unchanged.
        have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs
        have hih := ih u qH (by simpa using hQ2 u) s z hzx
        simpa using hih
      · -- READ: readlist grows by one; budget decrements by one (`0 < qH`).
        have hpos : 0 < qH := by
          rcases hQ1 with hno | hpos
          · exact absurd rfl hno
          · exact hpos
        have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$>
              roStep M s.1.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs
        have hih := ih cu.1 (qH - 1) (by simpa using hQ2 cu.1)
          ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)), mc.2 :: s.2) z hzx
        simp only [List.length_cons] at hih
        omega
      · -- SIGN: readlist untouched; budget unchanged.
        have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs
        have hih := ih alc.1.1 qH (by simpa using hQ2 alc.1.1)
          ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2) z hzx
        simpa using hih

omit [SampleableType Stmt] in
/-- **Per-step expected drawn-list length growth of the read-recording handler.** One step of
`deferredDrawReadImpl` grows the expected drawn-list length by at most `1/(1-p)` on a signing query
and by `0` on uniform / random-oracle-read queries (which leave the drawn list `s.1.1.2`
untouched). Identical to `deferredDrawImpl_step_expected_length_le` on the underlying deferred
state; the extra read-commit list is irrelevant to the drawn-list length. -/
lemma deferredDrawReadImpl_step_expected_drawnlist_length_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredReadState M Commit Chal,
      Pr[= z | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
        (z.2.1.1.2.length : ℝ≥0∞))
      ≤ (s.1.1.2.length : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · -- UNIFORM: state untouched, drawn list `s.1.1.2` preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawReadImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · -- READ: writes only the base cache / bad flag / readlist; drawn list `s.1.1.2` preserved.
    rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
              mc.2 :: s.2))) <$>
            roStep M s.1.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawReadImpl, StateT.run_mk]
      rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · -- SIGN: drawn list becomes `s.1.1.2 ++ alc.1.2`; expected new length ≤ 1/(1-p).
    rw [if_pos (by simp)]
    have hrun : (deferredDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul'
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)))
      (fun z => (z.2.1.1.2.length : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              ((s.1.1.2.length : ℝ≥0∞) + (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append]
          push_cast
          ring
      _ = (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (s.1.1.2.length : ℝ≥0∞)) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (alc.1.2.length : ℝ≥0∞) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ (s.1.1.2.length : ℝ≥0∞) + ENNReal.ofReal (1 / (1 - p_abort)) := by
          refine add_le_add ?_ ?_
          · rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          · exact le_trans (tsum_probOutput_run_ghostSignDrawBody_mul_length_le ids M pk sk msg
              hAbort maxAttempts s.1.1.1.1) (geomAttemptSum_le maxAttempts hp₀ hp)

omit [SampleableType Stmt] in
/-- **Run-level expected drawn-list length of the read-recording run.** By induction on `oa`, the
expected final drawn-list length of the read-recording run from a start state `s` is at most
`s.drawnlist.length + qSrem · (1/(1-p))`, where `qSrem` bounds the number of signing queries. The
read-recording counterpart of `deferredDraw_run_expected_length_le`: the drawn list evolves
identically (the recorded read-commit list never affects it), so the per-step charge
`deferredDrawReadImpl_step_expected_drawnlist_length_le` telescopes against the signing-query budget
exactly as before. -/
theorem deferredDrawRead_run_expected_drawnlist_length_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredReadState M Commit Chal),
        (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            (z.2.1.1.2.length : ℝ≥0∞))
          ≤ (s.1.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
          Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawReadImpl]
          · simp only [deferredDrawReadImpl, StateT.run_mk]
            rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawReadImpl])
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
            (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob x.1)).run x.2] * (z.2.1.1.2.length : ℝ≥0∞))
              ≤ (x.2.1.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
            (x.2.1.1.2.length : ℝ≥0∞)) ≤ (s.1.1.2.length : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob x.1)).run x.2] * (z.2.1.1.2.length : ℝ≥0∞))
            ≤ (s.1.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * (z.2.1.1.2.length : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                ((x.2.1.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                  (x.2.1.1.2.length : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                    ((x.2.1.1.2.length : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      (x.2.1.1.2.length : ℝ≥0∞) +
                    Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ ((s.1.1.2.length : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by gcongr
          _ ≤ (s.1.1.2.length : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by rw [add_assoc]; gcongr
      rcases t with (n | mc) | msg
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_drawnlist_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_drawnlist_length_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawReadImpl_step_expected_drawnlist_length_le ids M maxAttempts
            pk sk hp₀ hp hAbort (.inr msg) s
          rwa [if_pos (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **Per-step expected attempt-count growth of the read-recording handler.** One step of
`deferredDrawReadImpl` grows the expected combined size `drawnlist.length + signedlist.length` by at
most `1/(1-p)` on a signing query and by `0` on a uniform or random-oracle-read query (which leave
both lists untouched). The read-recording counterpart of
`deferredDrawImpl_step_expected_attemptCount_le`; the recorded read-commit list never affects the
drawn or signed lists, so the charge is identical. -/
lemma deferredDrawReadImpl_step_expected_attemptCount_le (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range t) ×
        DeferredReadState M Commit Chal,
      Pr[= z | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
        ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
      ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) +
          (if (t matches Sum.inr _) then ENNReal.ofReal (1 / (1 - p_abort)) else 0) := by
  classical
  rcases t with (n | mc) | msg
  · rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ (by simp [deferredDrawReadImpl]))
    intro z hz
    have hzs : z ∈ support ((fun u => (u, s)) <$>
        (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hz
    rw [support_map] at hzs
    obtain ⟨u, _, rfl⟩ := hzs; rfl
  · rw [if_neg (by simp), add_zero]
    refine le_of_eq (tsum_probOutput_mul_of_const_on_support _ ?_ ?_)
    · intro z hz
      have hzs : z ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
          (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
              mc.2 :: s.2))) <$>
            roStep M s.1.1.1.1 mc) := hz
      rw [support_map] at hzs
      obtain ⟨cu, _, rfl⟩ := hzs; rfl
    · simp only [deferredDrawReadImpl, StateT.run_mk]
      rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
  · rw [if_pos (by simp)]
    have hrun : (deferredDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run s =
        (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
          (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
          (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 := rfl
    rw [hrun]
    refine le_of_eq_of_le (tsum_probOutput_map_mul'
      ((ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1)
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)))
      (fun z => ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))) ?_
    calc _
        = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞) +
                (alc.1.2.length : ℝ≥0∞)) := by
          refine tsum_congr fun alc => ?_
          simp only [List.length_append, List.length_cons]
          push_cast
          ring
      _ = ((∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (1 : ℝ≥0∞))) +
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (alc.1.2.length : ℝ≥0∞)) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add]
      _ ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) +
            ENNReal.ofReal (1 / (1 - p_abort)) := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
          rw [add_assoc]
          gcongr
          refine le_trans (add_le_add_right
            (tsum_probOutput_run_ghostSignDrawBody_mul_length_le_tight ids M pk sk msg
              hAbort maxAttempts s.1.1.1.1) _) ?_
          rw [add_comm]
          refine le_trans (le_of_eq ?_) (geomSum_le hp₀ hp (maxAttempts + 1))
          rw [Finset.sum_range_succ']
          simp only [pow_zero]

omit [SampleableType Stmt] in
/-- **Run-level expected attempt count of the read-recording run.** By induction on `oa`, the
expected combined size `drawnlist.length + signedlist.length` of the read-recording run from a start
state `s` is at most `(s.drawnlist.length + s.signedlist.length) + qSrem · (1/(1-p))`, where `qSrem`
bounds the number of signing queries. The read-recording counterpart of
`deferredDraw_run_expected_attemptCount_le`. Subtracting the start signed-list length `l.length`
gives the attempt-count mean `≤ qSrem/(1-p)` used by the sound `#attempts`-form coincidence
bound. -/
theorem deferredDrawRead_run_expected_attemptCount_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredReadState M Commit Chal),
        (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
          ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) +
              (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      exact le_self_add
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind, tsum_probOutput_bind_mul]
      set c : ℝ≥0∞ := ENNReal.ofReal (1 / (1 - p_abort)) with hc
      have hmass : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
            (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
          Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s]) = 1 :=
        tsum_probOutput_eq_one' (by
          rcases t with (n | mc) | msg
          · simp [deferredDrawReadImpl]
          · simp only [deferredDrawReadImpl, StateT.run_mk]
            rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
          · simp [deferredDrawReadImpl])
      have hfold : ∀ (b : ℕ) (extra : ℝ≥0∞),
          (∀ x : (((unifSpec + (M × Commit →ₒ Chal)) +
              (M →ₒ Option (Commit × Resp))).Range t) × DeferredReadState M Commit Chal,
            (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob x.1)).run x.2] * ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
            ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
              ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + extra →
          extra + (b : ℝ≥0∞) * c ≤ (qSrem : ℝ≥0∞) * c →
          (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob x.1)).run x.2] * ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
        intro b extra hcont hstep hbudget
        calc (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob x.1)).run x.2] * ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
            ≤ ∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                (((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c) :=
              ENNReal.tsum_le_tsum fun x => by gcongr; exact hcont x
          _ = (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                  ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞)) + (b : ℝ≥0∞) * c := by
              rw [show (∑' x, Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                    (((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) + (b : ℝ≥0∞) * c))
                  = ∑' x, (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      ((x.2.1.1.2.length + x.2.1.1.1.2.length : ℕ) : ℝ≥0∞) +
                    Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk t).run s] *
                      ((b : ℝ≥0∞) * c)) from tsum_congr fun x => by rw [mul_add]]
              rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          _ ≤ (((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + extra) + (b : ℝ≥0∞) * c := by
              gcongr
          _ ≤ ((s.1.1.2.length + s.1.1.1.2.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * c := by
              rw [add_assoc]; gcongr
      rcases t with (n | mc) | msg
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inl n)) s
      · refine hfold qSrem 0 (fun x => ih x.1 qSrem (by simpa using hQ2 x.1) x.2) ?_ (by simp)
        simpa using deferredDrawReadImpl_step_expected_attemptCount_le ids M maxAttempts pk sk
          hp₀ hp hAbort (.inl (.inr mc)) s
      · have hpos : 0 < qSrem := by
          rcases hQ1 with hno | hpos
          · exact absurd (by simp) hno
          · exact hpos
        refine hfold (qSrem - 1) c (fun x => ih x.1 (qSrem - 1) (by simpa using hQ2 x.1) x.2) ?_ ?_
        · have hstep := deferredDrawReadImpl_step_expected_attemptCount_le ids M maxAttempts
            pk sk hp₀ hp hAbort (.inr msg) s
          rwa [if_pos (by rfl), ← hc] at hstep
        · rw [add_comm, ← add_one_mul,
            show ((qSrem - 1 : ℕ) : ℝ≥0∞) + 1 = (qSrem : ℝ≥0∞) by
              have : qSrem - 1 + 1 = qSrem := by omega
              rw [← this]; push_cast; ring]

omit [SampleableType Stmt] in
/-- **The read-recording run never fails.** Every step of `deferredDrawReadImpl` pushes forward a
non-failing `ProbComp`, so the whole fold has zero failure mass. -/
theorem deferredDrawRead_run_neverFail {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredReadState M Commit Chal),
      Pr[⊥ | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s; simp [simulateQ_pure, StateT.run_pure]
  | query_bind t ob ih =>
      intro s
      rw [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff]
      refine ⟨?_, fun x _ => ih x.1 x.2⟩
      rcases t with (n | mc) | msg
      · simp [deferredDrawReadImpl]
      · simp only [deferredDrawReadImpl]
        rcases hg : s.1.1.1.1 mc with _ | v <;> simp [roStep, hg]
      · simp [deferredDrawReadImpl]

omit [SampleableType Stmt] in
/-- **The signed-message list of the read-recording run grows.** From any start state the recorded
signed-message list only ever gets longer, so its start length `l.length` is a lower bound on every
reachable final length. -/
theorem deferredDrawRead_run_signed_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredReadState M Commit Chal)
      (z : γ × DeferredReadState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.1.1.2.length ≤ z.2.1.1.1.2.length := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine le_trans ?_ (ih x.1 x.2 z hzx)
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; simp

omit [SampleableType Stmt] in
/-- **The drawn-list of the read-recording run grows.** From any start state the recorded drawn
(rejected-commit) list only ever gets longer: uniform and read steps leave it untouched, signing
steps append the body's rejected draws. So the start length is a lower bound on every reachable
final length. -/
theorem deferredDrawRead_run_drawn_prefix {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (s : DeferredReadState M Commit Chal)
      (z : γ × DeferredReadState M Commit Chal),
      z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s) →
      s.1.1.2.length ≤ z.2.1.1.2.length := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro s z hz
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact le_rfl
  | query_bind t ob ih =>
      intro s z hz
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      refine le_trans ?_ (ih x.1 x.2 z hzx)
      rcases t with (n | mc) | msg
      · have hxs : x ∈ support ((fun u => (u, s)) <$>
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
        rw [support_map] at hxs
        obtain ⟨u, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
            (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc) := hx
        rw [support_map] at hxs
        obtain ⟨cu, _, rfl⟩ := hxs; exact le_rfl
      · have hxs : x ∈ support ((fun alc : (Option (Commit × Resp) × List Commit) ×
            (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1) := hx
        rw [support_map] at hxs
        obtain ⟨alc, _, rfl⟩ := hxs; simp

omit [SampleableType Stmt] in
/-- **Read-recording attempt-count mean.** The constructed attempt count
`(drawnlist.length) + (signedlist.length - l.length)` (= #rejects + #signing-queries, the count that
soundly dominates the consumed-attempt positions) of the read-recording run from the empty-draw
start `((((re, l), []), false), [])` has mean at most `qSrem/(1-p)`. Mirrors
`deferredDraw_attemptKn_mean_le`: recover the total combined size by adding back `l.length`, valid
because `l` is a signed-list prefix (`deferredDrawRead_run_signed_prefix`); bound by the run-level
attempt-count fold `deferredDrawRead_run_expected_attemptCount_le`, then cancel `l.length` (run mass
`1`, `deferredDrawRead_run_neverFail`). -/
theorem deferredDrawRead_attemptKn_mean_le {γ : Type} (pk : Stmt) (sk : Wit)
    {p_abort : ℝ} (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ) (hQ : oa.IsQueryBoundP (· matches Sum.inr _) qSrem)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
      ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
  classical
  set run : ProbComp (γ × DeferredReadState M Commit Chal) :=
    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run ((((re, l), []), false), [])
    with hrun
  have hmass : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run]) = 1 := by
    rw [hrun]
    exact tsum_probOutput_eq_one'
      (deferredDrawRead_run_neverFail ids M maxAttempts pk sk oa ((((re, l), []), false), []))
  -- Recover the total combined size by adding back `l.length`; the start drawn list is empty.
  have hsplit : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
        ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
        ((l.length : ℕ) : ℝ≥0∞)
      = ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞) := by
    rw [show ((l.length : ℕ) : ℝ≥0∞)
          = ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] * ((l.length : ℕ) : ℝ≥0∞) by
        rw [ENNReal.tsum_mul_right, hmass, one_mul]]
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    rw [← mul_add]
    by_cases hz : z ∈ support run
    · have hpre : l.length ≤ z.2.1.1.1.2.length := by
        have := deferredDrawRead_run_signed_prefix ids M maxAttempts pk sk oa
          ((((re, l), []), false), []) z (by rwa [hrun] at hz)
        simpa using this
      congr 1
      rw [← Nat.cast_add]
      congr 1
      omega
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul]
  -- The total combined size is bounded by `l.length + qSrem/(1-p)`; cancel `l.length`.
  have htot : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
        ((z.2.1.1.2.length + z.2.1.1.1.2.length : ℕ) : ℝ≥0∞))
      ≤ ((l.length : ℕ) : ℝ≥0∞) + (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [hrun]
    have := deferredDrawRead_run_expected_attemptCount_le ids M maxAttempts pk sk hp₀ hp hAbort
      oa qSrem hQ ((((re, l), []), false), [])
    simpa using this
  -- Subtract `l.length` from both sides of `hsplit ≤ htot` (it is a finite quantity ≤ both).
  have hle : (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
        ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)) +
        ((l.length : ℕ) : ℝ≥0∞)
      ≤ ((qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort))) + ((l.length : ℕ) : ℝ≥0∞) := by
    rw [hsplit, add_comm ((qSrem : ℝ≥0∞) * _)]; exact htot
  exact ENNReal.le_of_add_le_add_right (by simp) hle

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq Commit] in
/-- **Splitting an i.i.d. front draw block.** Drawing `n + m` independent commitment draws into a
list is the same computation as drawing the first `n` and then the last `m` and concatenating: the
front block factors into independent sub-blocks. This is the structural identity that, with the
i.i.d. resampling commute, lets the per-query draw blocks accumulate into one front tape. -/
lemma drawList_commit_add (pk : Stmt) (sk : Wit) (n m : ℕ) :
    OracleComp.drawList (ids.commit pk sk) (n + m) =
      OracleComp.drawList (ids.commit pk sk) n >>= fun a =>
        OracleComp.drawList (ids.commit pk sk) m >>= fun b => pure (a ++ b) := by
  classical
  induction n with
  | zero => simp [OracleComp.drawList]
  | succ n ih =>
      rw [Nat.succ_add, OracleComp.drawList, OracleComp.drawList, ih]
      simp only [bind_assoc, pure_bind, List.cons_append]

omit [SampleableType Stmt] [SampleableType Chal] [DecidableEq Commit] in
/-- **Front draw blocks have a deterministic length.** Every list in the support of
`drawList (ids.commit pk sk) n` has length exactly `n`: the block always draws `n` keys. This lets
the `take`/`drop` split of an over-provisioned tape resolve to the per-query block and its
remainder. -/
lemma length_mem_support_drawList_commit (pk : Stmt) (sk : Wit) (n : ℕ)
    (ws : List (Commit × PrvState))
    (hws : ws ∈ support (OracleComp.drawList (ids.commit pk sk) n)) :
    ws.length = n := by
  classical
  induction n generalizing ws with
  | zero =>
      simp only [OracleComp.drawList, support_pure, Set.mem_singleton_iff] at hws
      subst hws; rfl
  | succ n ih =>
      rw [OracleComp.drawList] at hws
      simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hws
      obtain ⟨w, hw, ws', hws', rfl⟩ := hws
      simp [ih ws' hws']

/-! ### Fold-level tape factorization (the framework infrastructure)

The body-level half of the tape factorization
(`evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody`)
recasts *one* signing body's inline attempt draws as consumption from a pre-drawn tape. The
*fold-level* half — built here — lifts that across the opaque adversary `simulateQ (oa)` fold: every
interleaved signing query's draw block commutes to the very front, so the whole run distributes as

  `drawList (ids.commit pk sk) L >>= fun tape => (simulateQ tapeDrawReadImpl oa).run (s, tape)`,

a single independent front draw block of `L := maxAttempts · #signing-queries` commitments followed
by a tape-*consuming* run. This is the genuine framework content the campaign reduced to: once the
draws are front-loaded, the recorded drawn list is a function of the tape and the value-free read
list is a function of the non-tape randomness, so the read list is independent of the tape.

The tape-consuming handler `tapeDrawReadImpl` carries a draw tape in its state; a signing query
consumes the first `maxAttempts` tape entries (running `tapeSignBody` on them and dropping them)
instead of drawing inline, while reads/uniform behave exactly as `deferredDrawReadImpl`. The
fold equality is proved by `inductionOn oa`: at a read/uniform step the answer is independent of the
tape so the front draw block commutes trivially; at a signing step the banked per-body factorization
splices in the body's `drawList maxAttempts` block, which then commutes to the front of the
remaining tape via the i.i.d. resampling commute `evalDist_bind_comm_probComp`. -/

/-- The tape-consuming read-recording handler. Its state extends `DeferredReadState` with a *draw
tape* `List (Commit × PrvState)`: a signing query consumes the first `maxAttempts` entries of the
tape (running the tape-consuming body `tapeSignBody` on them and dropping them from the tape)
instead of drawing each attempt's commitment inline; uniform and random-oracle-read queries behave
exactly as `deferredDrawReadImpl` and leave the tape untouched. Over-provisioning the tape (length
`maxAttempts · #signing-queries`) makes the front-loaded draw block independent of the value-free
read list. -/
noncomputable def tapeDrawReadImpl (pk : Stmt) (sk : Wit) :
    QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (DeferredReadState M Commit Chal × List (Commit × PrvState)) ProbComp) :=
  fun t => match t with
  | .inl (.inl n) => StateT.mk fun s =>
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
  | .inl (.inr mc) => StateT.mk fun s =>
      (fun cu => (cu.1, (((((cu.2, s.1.1.1.1.2), s.1.1.1.2), s.1.1.2 || decide (mc.2 ∈ s.1.1.1.2)),
          mc.2 :: s.1.2), s.2))) <$>
        roStep M s.1.1.1.1.1 mc
  | .inr msg => StateT.mk fun s =>
      (fun alc => (alc.1.1, (((((alc.2, msg :: s.1.1.1.1.2), s.1.1.1.2 ++ alc.1.2), s.1.1.2),
          s.1.2), s.2.drop maxAttempts))) <$>
        (tapeSignBody ids M pk sk msg (s.2.take maxAttempts)).run s.1.1.1.1.1

omit [SampleableType Stmt] in
/-- **One-step unfolding of `tapeDrawReadImpl` on a uniform query.** -/
lemma tapeDrawReadImpl_run_unif (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : DeferredReadState M Commit Chal × List (Commit × PrvState)) :
    (tapeDrawReadImpl ids M maxAttempts pk sk (.inl (.inl n))).run s =
      (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl

omit [SampleableType Stmt] in
/-- **One-step unfolding of `tapeDrawReadImpl` on a random-oracle read query.** -/
lemma tapeDrawReadImpl_run_read (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : DeferredReadState M Commit Chal × List (Commit × PrvState)) :
    (tapeDrawReadImpl ids M maxAttempts pk sk (.inl (.inr mc))).run s =
      (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
        (cu.1, (((((cu.2, s.1.1.1.1.2), s.1.1.1.2), s.1.1.2 || decide (mc.2 ∈ s.1.1.1.2)),
            mc.2 :: s.1.2), s.2))) <$>
        roStep M s.1.1.1.1.1 mc := rfl

omit [SampleableType Stmt] in
/-- **One-step unfolding of `tapeDrawReadImpl` on a signing query.** The body consumes the first
`maxAttempts` tape entries (via `tapeSignBody`), the drawn list is extended by the recorded rejected
commitments, and the tape advances by `maxAttempts`. -/
lemma tapeDrawReadImpl_run_sign (pk : Stmt) (sk : Wit) (msg : M)
    (s : DeferredReadState M Commit Chal × List (Commit × PrvState)) :
    (tapeDrawReadImpl ids M maxAttempts pk sk (.inr msg)).run s =
      (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
        (alc.1.1, (((((alc.2, msg :: s.1.1.1.1.2), s.1.1.1.2 ++ alc.1.2), s.1.1.2),
            s.1.2), s.2.drop maxAttempts))) <$>
        (tapeSignBody ids M pk sk msg (s.2.take maxAttempts)).run s.1.1.1.1.1 := rfl

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- **Answer-irrelevant cross-step commute (the read/uniform inductive step).** A query step whose
answer and new non-tape state are produced by a tape-*preserving* `ProbComp` `step` (the uniform and
random-oracle-read steps both leave the tape untouched) commutes with the front draw block: pushing
the per-continuation front block to the very front past the answer is the i.i.d. resampling commute
`evalDist_bind_comm_probComp`. Given the inductive hypothesis `hcont` (the continuation run factors
as a front block followed by the tape-consuming continuation), the whole step factors likewise. -/
theorem evalDist_tapePreserving_step_commute {γ Ans : Type}
    (step : ProbComp (Ans × DeferredReadState M Commit Chal))
    (L : ℕ)
    (defCont : Ans → DeferredReadState M Commit Chal →
      ProbComp (γ × DeferredReadState M Commit Chal))
    (tapeCont : Ans → DeferredReadState M Commit Chal × List (Commit × PrvState) →
      ProbComp (γ × (DeferredReadState M Commit Chal × List (Commit × PrvState))))
    (pk : Stmt) (sk : Wit)
    (hcont : ∀ (a : Ans) (s' : DeferredReadState M Commit Chal),
      𝒟[defCont a s'] =
        𝒟[OracleComp.drawList (ids.commit pk sk) L >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$> tapeCont a (s', tape)]) :
    𝒟[step >>= fun p => defCont p.1 p.2] =
      𝒟[OracleComp.drawList (ids.commit pk sk) L >>= fun tape =>
          (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
              (p.1, p.2.1)) <$>
            (((fun p : Ans × DeferredReadState M Commit Chal => (p.1, (p.2, tape))) <$> step)
              >>= fun p => tapeCont p.1 p.2)] :=
  -- A direct instance of the generic answer-irrelevant tape commute: the front draw block is the
  -- `drawList (ids.commit pk sk) L` tape and `proj` discards the spent suffix.
  OracleComp.DeferredSampling.evalDist_step_commute_tape step
    (OracleComp.drawList (ids.commit pk sk) L)
    (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) => (p.1, p.2.1))
    defCont tapeCont hcont

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] in
/-- **Tape-combine reconciliation.** A front block drawn in two pieces — `maxAttempts` then
`maxAttempts · q'` — feeding a continuation `g blk rest` is the same computation as drawing the
whole `maxAttempts · (q'+1)` block at once and splitting it with `take`/`drop`: the first
`maxAttempts` entries are the body block, the remainder is the leftover tape. Uses
`drawList_commit_add` to split and the deterministic block length
`length_mem_support_drawList_commit` to resolve `take`/`drop`. -/
theorem drawList_combine_take_drop {δ : Type} (pk : Stmt) (sk : Wit) (q' : ℕ)
    (g : List (Commit × PrvState) → List (Commit × PrvState) → ProbComp δ) :
    𝒟[OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
        OracleComp.drawList (ids.commit pk sk) (maxAttempts * q') >>= fun rest => g blk rest]
      = 𝒟[OracleComp.drawList (ids.commit pk sk) (maxAttempts * (q' + 1)) >>= fun tape =>
          g (tape.take maxAttempts) (tape.drop maxAttempts)] := by
  classical
  rw [show maxAttempts * (q' + 1) = maxAttempts + maxAttempts * q' by ring,
    drawList_commit_add ids pk sk maxAttempts (maxAttempts * q'), bind_assoc]
  -- On the support of the first block, its length is `maxAttempts`, so `take`/`drop` resolve.
  refine evalDist_bind_congr (fun blk hblk => ?_)
  have hlen : blk.length = maxAttempts := length_mem_support_drawList_commit ids pk sk _ blk hblk
  rw [bind_assoc]
  refine evalDist_bind_congr_left _ _ _ (fun rest => ?_)
  rw [pure_bind, List.take_left' hlen, List.drop_left' hlen]

omit [SampleableType Stmt] in
theorem evalDist_defSignStep_splice {δ : Type} (pk : Stmt) (sk : Wit) (msg : M)
    (s : DeferredReadState M Commit Chal)
    (k : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache →
      ProbComp δ) :
    𝒟[(ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 >>= k] =
      𝒟[OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
          (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1 >>= k] := by
  rw [show (OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
        (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1 >>= k)
      = (OracleComp.drawList (ids.commit pk sk) maxAttempts >>= fun blk =>
          (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1) >>= k from by rw [bind_assoc]]
  rw [evalDist_bind,
    evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody ids M pk sk msg maxAttempts s.1.1.1.1,
    ← evalDist_bind]

omit [SampleableType Stmt] in
/-- **Sign-step cross-step commute (the crux inductive step).** The deferred-draw sign step,
composed with the deferred continuation, factors as a single front draw block of
`maxAttempts·(q'+1)` commitments followed by the tape-consuming sign step + tape continuation. The
genuine framework content: the body's `maxAttempts` draw block splices to the front via the per-body
factorization (`evalDist_defSignStep_splice`); the continuation's `maxAttempts·q'` block (supplied
by the inductive hypothesis `hcont`) commutes past the body via the i.i.d. resampling commute
(`evalDist_bind_comm_probComp`); the two blocks combine into one `maxAttempts·(q'+1)` block split by
`take`/`drop` (`drawList_combine_take_drop`), exactly the tape the tape-consuming sign step
consumes. -/
theorem evalDist_signStep_commute {γ : Type} (pk : Stmt) (sk : Wit) (msg : M)
    (s : DeferredReadState M Commit Chal) (q' : ℕ)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
        (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hcont : ∀ (a : ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
        (s' : DeferredReadState M Commit Chal),
      𝒟[(simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob a)).run s'] =
        𝒟[OracleComp.drawList (ids.commit pk sk) (maxAttempts * q') >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob a)).run (s', tape)]) :
    𝒟[(deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s >>= fun p =>
        (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2] =
      𝒟[OracleComp.drawList (ids.commit pk sk) (maxAttempts * (q' + 1)) >>= fun tape =>
          (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
              (p.1, p.2.1)) <$>
            ((tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run (s, tape) >>= fun p =>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2)] := by
  classical
  -- LHS: fold the deferred sign step's map into the body bind, then splice the front block.
  rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s >>= (fun p =>
        (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2)
      = (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 >>= fun alc =>
          (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
            (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)
      from by
        rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s
              = (fun alc : (Option (Commit × Resp) × List Commit) ×
                  (M × Commit →ₒ Chal).QueryCache =>
                  (alc.1.1, ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))) <$>
                (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1 from rfl]
        simp [bind_map_left]]
  rw [evalDist_defSignStep_splice ids M maxAttempts pk sk msg s
    (fun alc => (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
      (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))]
  -- Rewrite the continuation by `hcont`, under the leading `drawList maxAttempts` and body binds.
  rw [evalDist_bind_congr (mx := OracleComp.drawList (ids.commit pk sk) maxAttempts)
    (fun blk _ => evalDist_bind_congr (mx := (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1)
      (fun alc _ => hcont alc.1.1 ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)))]
  -- Commute the continuation's `maxAttempts·q'` block to the front past the body.
  rw [evalDist_bind_congr (mx := OracleComp.drawList (ids.commit pk sk) maxAttempts)
    (fun blk _ => evalDist_bind_comm_probComp ((tapeSignBody ids M pk sk msg blk).run s.1.1.1.1)
      (OracleComp.drawList (ids.commit pk sk) (maxAttempts * q'))
      (fun alc tape => (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
          (p.1, p.2.1)) <$>
        (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk)
          (ob alc.1.1)).run
            (((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2), tape)))]
  -- Combine the two front blocks into one `maxAttempts·(q'+1)` block split by `take`/`drop`.
  rw [drawList_combine_take_drop ids maxAttempts pk sk q'
    (fun blk rest => (tapeSignBody ids M pk sk msg blk).run s.1.1.1.1 >>= fun alc =>
      (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
          (p.1, p.2.1)) <$>
        (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk)
          (ob alc.1.1)).run
            (((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2), rest))]
  -- Match the RHS: the tape sign step consumes `take maxAttempts` and threads `drop maxAttempts`.
  refine evalDist_bind_congr_left _ _ _ (fun tape => ?_)
  rw [show (tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run (s, tape)
        = (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
            (alc.1.1, (((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2),
              tape.drop maxAttempts))) <$>
          (tapeSignBody ids M pk sk msg (tape.take maxAttempts)).run s.1.1.1.1 from rfl]
  simp [bind_map_left, map_bind]

omit [SampleableType Stmt] in
/-- **The fold-level tape factorization (the framework lemma).** By induction on the adversary
computation `oa`, the read-recording deferred-draw run distributes as a single front draw block of
`maxAttempts · qSrem` commitments followed by a tape-consuming run:

`𝒟[(simulateQ deferredDrawReadImpl oa).run s]`
`  = 𝒟[drawList (ids.commit pk sk) (maxAttempts · qSrem) >>= fun tape =>`
`        (simulateQ tapeDrawReadImpl oa).run (s, tape)]`,

where `qSrem` bounds the number of signing queries of `oa` (the `(· matches .inr _)` component of
`signHashQueryBound`). The tape is over-provisioned (length `maxAttempts · qSrem`); each signing
query consumes its `maxAttempts`-prefix and the unused suffix is discarded on early accept.

The proof inducts on `oa`. At a **read/uniform** step the query answer is independent of the tape,
so the front draw block commutes past it (the i.i.d. resampling commute
`evalDist_bind_comm_probComp`),
matching the inductive hypothesis for the continuation. At a **signing** step the banked per-body
factorization `evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody` recasts the body's inline draws
as a `drawList maxAttempts` block; that block is split off the front via `drawList_commit_add` (the
remaining `maxAttempts · (qSrem-1)` block feeding the continuation by the inductive hypothesis) and
commuted to the front past the answer-irrelevant continuation. This is the genuine framework content
("answer-irrelevant per-step draws factor to a front tape in `simulateQ`"). -/
theorem evalDist_deferredDrawRead_eq_drawList_tapeDrawRead {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ) :
    ∀ (qSrem : ℕ), oa.IsQueryBoundP (· matches Sum.inr _) qSrem →
      ∀ (s : DeferredReadState M Commit Chal),
        𝒟[(simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] =
          𝒟[OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
              (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                  (p.1, p.2.1)) <$>
                (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run (s, tape)] := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a =>
      intro qSrem _ s
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      rw [evalDist_bind_const_neverFails _ (OracleComp.probFailure_drawList _ _)]
  | query_bind t ob ih =>
      intro qSrem hQ s
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      rcases t with (n | mc) | msg
      · -- UNIFORM: the answer is independent of the tape; commute the front block past the draw.
        have hqs : (if (match (Sum.inl (Sum.inl n) :
              ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind]
        rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run s
              = (fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n
            from rfl]
        -- The tape uniform step is the deferred step with the tape inserted (`Functor.map_map`).
        rw [show (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              ((tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run (s, tape)
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (((fun p : (((unifSpec + (M × Commit →ₒ Chal)) +
                  (M →ₒ Option (Commit × Resp))).Range (Sum.inl (Sum.inl n))) ×
                    DeferredReadState M Commit Chal => (p.1, (p.2, tape))) <$>
                  ((fun u => (u, s)) <$>
                    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n))
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            from by funext tape; rw [tapeDrawReadImpl_run_unif, Functor.map_map]; rfl]
        exact evalDist_tapePreserving_step_commute ids M
          ((fun u => (u, s)) <$> (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n)
          (maxAttempts * qSrem)
          (fun a s' => (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob a)).run s')
          (fun a st => (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob a)).run st)
          pk sk (fun a s' => ih a qSrem (hQ2 a) s')
      · -- READ: the answer is `roStep` (real layer), independent of the tape; same commute.
        have hqs : (if (match (Sum.inl (Sum.inr mc) :
              ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind]
        rw [show (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run s
              = (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
                  (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                    mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc
            from rfl]
        rw [show (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              ((tapeDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run (s, tape)
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            = (fun tape => (fun p :
                γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (((fun p : Chal × DeferredReadState M Commit Chal => (p.1, (p.2, tape))) <$>
                  ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
                    (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                      mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc))
                >>= fun p =>
                  (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob p.1)).run p.2))
            from by funext tape; rw [tapeDrawReadImpl_run_read, Functor.map_map]; rfl]
        exact evalDist_tapePreserving_step_commute ids M
          ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc)
          (maxAttempts * qSrem)
          (fun a s' => (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob a)).run s')
          (fun a st => (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) (ob a)).run st)
          pk sk (fun a s' => ih a qSrem (hQ2 a) s')
      · -- SIGN: the crux. Splice the per-body draw block to the front past the continuation.
        have hpos : 0 < qSrem := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        clear hQ1
        have hqs : (if (match (Sum.inr msg :
              ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain) with
            | Sum.inr _ => true | _ => false) = true then qSrem - 1 else qSrem) = qSrem - 1 := rfl
        rw [hqs] at hQ2
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map, StateT.run_bind]
        rw [show qSrem = (qSrem - 1) + 1 from by omega]
        exact evalDist_signStep_commute ids M maxAttempts pk sk msg s (qSrem - 1) ob
          (fun a s' => ih a (qSrem - 1) (hQ2 a) s')

omit [SampleableType Stmt] in
/-- **The atomic value-free charge (the irreducible probabilistic kernel).** One fresh raw
commitment draw `w ← ids.commit pk sk`, *independent of* a value-free list `rl`, contributes
expected multiplicity `E[rl.count w.1] ≤ ε · rl.length`: each of the `rl.length` slots of `rl` is
hit by the fresh draw with probability `Pr[= slot | Prod.fst <$> ids.commit pk sk] ≤ ε` (`hGuess`).

This is the single source of the `ε` in the ghost-read bound. It is purely the per-draw mass bound
combined with the independence of the draw from the (value-free) read list; the structural content
of the full charge is to exhibit each recorded rejected draw of the tape run in exactly this
independent-of-the-readlist position (the value-substitution at rejected tape positions). -/
private lemma tsum_probOutput_commit_mul_count_le {C P : Type} [DecidableEq C]
    (commit : ProbComp (C × P)) (rl : List C) (ε : ℝ)
    (hGuess : ∀ cm : C, Pr[= cm | Prod.fst <$> commit] ≤ ENNReal.ofReal ε) :
    (∑' w : C × P, Pr[= w | commit] * (rl.count w.1 : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * (rl.length : ℝ≥0∞) :=
  OracleComp.DeferredSampling.tsum_probOutput_fresh_mul_count_le commit rl ε hGuess

omit [SampleableType Stmt] in
/-- **Value-substitution: the recorded read list is independent of the drawn-list content.** The
expected multiplicity `E[readlist.count w]` of any fixed commitment `w` in the recorded read list of
the read-recording run depends only on the start *real cache*, *signed list*, and *read list* — not
on the start *drawn list* `D` nor the start *bad flag* `b`. This is the structural value-freeness at
the heart of the ghost-read bound: the recorded reads answer via `roStep` on the real layer and
never the drawn (rejected) values, so changing the drawn list (or the bad flag, which is write-only
and never gates control flow) leaves the read-list marginal unchanged.

Formally the expectation is invariant under both drawn-list and bad-flag start values. Proved by
induction on `oa`:
* **pure** — the read list is the start one (independent of `D`, `b`).
* **uniform** — the draw is forwarded and the drawn list / bad flag / read list are untouched; the
  inductive hypothesis applies to the unchanged-`D` continuation.
* **read** — the read list grows by exactly `mc.2` (the same regardless of `D`); the bad flag
  updates to `b || (mc.2 ∈ D)` (which *does* depend on `D`), but since the inductive hypothesis is
  quantified over *all* bad-flag values, the two `D`-runs still agree.
* **sign** — the body draws are the same regardless of `D`, `b`; the drawn list grows by the body's
  rejected commitments and the bad flag is preserved, and the inductive hypothesis (quantified over
  all `D`) closes the differing-drawn-list continuations. -/
theorem deferredDrawRead_run_count_dl_invariant {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (w : Commit) (re : (M × Commit →ₒ Chal).QueryCache) (sgn : List M)
    (rl : List Commit) :
    ∀ (D₁ : List Commit) (b₁ : Bool) (D₂ : List Commit) (b₂ : Bool),
      (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, sgn), D₁), b₁), rl)] * (z.2.2.count w : ℝ≥0∞))
        = ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                ((((re, sgn), D₂), b₂), rl)] * (z.2.2.count w : ℝ≥0∞) := by
  induction oa using OracleComp.inductionOn generalizing re sgn rl with
  | pure a =>
      intro D₁ b₁ D₂ b₂
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
  | query_bind t ob ih =>
      intro D₁ b₁ D₂ b₂
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, tsum_probOutput_bind_mul]
      rcases t with (n | mc) | msg
      · -- UNIFORM: drawn list / bad flag / read list untouched; forward draw.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inl (Sum.inl n))) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (z.2.2.count w : ℝ≥0∞) with hG
        have hx₁ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run
              ((((re, sgn), D₁), b₁), rl)) =
            (fun u => (u, ((((re, sgn), D₁), b₁), rl))) <$>
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
        have hx₂ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inl n))).run
              ((((re, sgn), D₂), b₂), rl)) =
            (fun u => (u, ((((re, sgn), D₂), b₂), rl))) <$>
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n := rfl
        rw [hx₁, hx₂]
        refine (tsum_probOutput_map_mul' _ _ G).trans
          ((tsum_congr fun u => ?_).trans (tsum_probOutput_map_mul' _ _ G).symm)
        exact congrArg _ (ih u re sgn rl D₁ b₁ D₂ b₂)
      · -- READ: read list grows by `mc.2` (independent of `D`); the bad flag updates to
        -- `b || (mc.2 ∈ D)` (D-dependent), but `ih` is quantified over *all* bad flags.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inl (Sum.inr mc))) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (z.2.2.count w : ℝ≥0∞) with hG
        have hx₁ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run
              ((((re, sgn), D₁), b₁), rl)) =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, sgn), D₁), b₁ || decide (mc.2 ∈ D₁)), mc.2 :: rl))) <$>
              roStep M re mc := rfl
        have hx₂ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inl (Sum.inr mc))).run
              ((((re, sgn), D₂), b₂), rl)) =
            (fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, sgn), D₂), b₂ || decide (mc.2 ∈ D₂)), mc.2 :: rl))) <$>
              roStep M re mc := rfl
        rw [hx₁, hx₂]
        refine (tsum_probOutput_map_mul' _ _ G).trans
          ((tsum_congr fun cu => ?_).trans (tsum_probOutput_map_mul' _ _ G).symm)
        exact congrArg _
          (ih cu.1 cu.2 sgn (mc.2 :: rl) D₁ (b₁ || decide (mc.2 ∈ D₁)) D₂
            (b₂ || decide (mc.2 ∈ D₂)))
      · -- SIGN: the body draws are `D`-independent; drawn list grows by the body's rejected
        -- commitments and the bad flag is preserved; `ih` (over all `D`) closes the continuations.
        set G : (((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range
            (Sum.inr msg)) × DeferredReadState M Commit Chal → ℝ≥0∞ :=
          fun x => ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (z.2.2.count w : ℝ≥0∞) with hG
        have hx₁ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run
              ((((re, sgn), D₁), b₁), rl)) =
            (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
              (alc.1.1, ((((alc.2, msg :: sgn), D₁ ++ alc.1.2), b₁), rl))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run re := rfl
        have hx₂ : ((deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run
              ((((re, sgn), D₂), b₂), rl)) =
            (fun alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache =>
              (alc.1.1, ((((alc.2, msg :: sgn), D₂ ++ alc.1.2), b₂), rl))) <$>
              (ghostSignDrawBody ids M pk sk msg maxAttempts).run re := rfl
        rw [hx₁, hx₂]
        refine (tsum_probOutput_map_mul' _ _ G).trans
          ((tsum_congr fun alc => ?_).trans (tsum_probOutput_map_mul' _ _ G).symm)
        exact congrArg _
          (ih alc.1.1 alc.2 (msg :: sgn) rl (D₁ ++ alc.1.2) b₁ (D₂ ++ alc.1.2) b₂)

omit [SampleableType Stmt] in
/-- **The value-substituted continuation read-multiplicity functional is drawn-invariant.** A
restatement of `deferredDrawRead_run_count_dl_invariant` reorganised for the body charge: the
expected read-multiplicity `E[Σ_{rc ∈ readlist} R.count rc]` of a *fixed* commit list `R` against
the continuation's recorded read list is invariant under the continuation's start drawn list (and
bad flag). The reads answer via `roStep` on the real layer, never the drawn (rejected) values, so
adding `R` (or any list) to the start drawn list does not change the read-list marginal. -/
theorem deferredDrawRead_run_sum_count_dl_invariant {γ : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (R : List Commit) (re : (M × Commit →ₒ Chal).QueryCache) (sgn : List M)
    (rl : List Commit) (D₁ : List Commit) (b₁ : Bool) (D₂ : List Commit) (b₂ : Bool) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, sgn), D₁), b₁), rl)] * ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
      = ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, sgn), D₂), b₂), rl)] * ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) := by
  classical
  induction R with
  | nil => simp
  | cons w R ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [show ∀ (D : List Commit) (b : Bool),
            (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                  ((((re, sgn), D), b), rl)] *
                (((z.2.2.count w : ℕ) : ℝ≥0∞) + ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞)))
              = (∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                      ((((re, sgn), D), b), rl)] * ((z.2.2.count w : ℕ) : ℝ≥0∞))
                + ∑' z : γ × DeferredReadState M Commit Chal,
                    Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
                        ((((re, sgn), D), b), rl)] *
                      ((R.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) from
          fun D b => by rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
      rw [deferredDrawRead_run_count_dl_invariant ids M maxAttempts pk sk oa w re sgn rl
            D₁ b₁ D₂ b₂, ih, ← ENNReal.tsum_add]
      exact tsum_congr fun z => by rw [mul_add]

omit [SampleableType Stmt] in
/-- **One step of the constant-length body charge (the genuine per-attempt induction step).** The
`succ` case of `ghostSignDrawBody_continuation_charge`: peel the head commit draw `ws` (kept
*averaged* — the head `ε`-kernel needs the full `ids.commit` marginal, a per-`ws` bound is false),
the challenge and the response, and case on the accept/reject branch. On *accept* the body records
nothing (charge `0`). On *reject* the recorded rejects are `ws.1 :: rec-rejects`; the
read-multiplicity splits into the head `z.readlist.count ws.1` (paid by the unconditional `+1` via
the value-substituted, gate-dropped marginal `ε`-kernel) and the recursive body charge (the
inductive hypothesis `ih` at the extended start drawn list `dr ++ [ws.1]`). The body never fails, so
the full-mass identities make the head `≤ L₀` match the RHS `+1`. -/
theorem ghostSignDrawBody_succ_charge {γ : Type}
    (qH : ℕ) (ε : ℝ) (_hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (msg : M)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hob : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (sgn : List M) (rl : List Commit) (bad : Bool) (n : ℕ)
    (re : (M × Commit →ₒ Chal).QueryCache) (dr : List Commit)
    (ih : ∀ (re : (M × Commit →ₒ Chal).QueryCache) (dr : List Commit),
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) *
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞)) :
    (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | (ghostSignDrawBody ids M pk sk msg (n + 1)).run re] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
              ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) *
        ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg (n + 1)).run re] *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
  classical
  set L₀ : ℝ≥0∞ := ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) with hL₀
  -- The continuation run never fails, so its output mass is `1`.
  have hcontMass : ∀ (u : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
      (cache : (M × Commit →ₒ Chal).QueryCache) (D : List Commit),
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run
            ((((cache, sgn), D), bad), rl)]) = 1 := fun u cache D =>
    tsum_probOutput_eq_one'
      (deferredDrawRead_run_neverFail ids M maxAttempts pk sk (ob u) _)
  -- The signing body never fails, so its output mass is `1`.
  have hbodyMass : ∀ (re' : (M × Commit →ₒ Chal).QueryCache),
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re']) = 1 := by
    intro re'
    exact tsum_probOutput_eq_one' (by simp)
  -- Deterministic continuation-readlist bound: every continuation run started at read list `rl`
  -- with read budget `qH` records `≤ rl.length + qH` reads.
  have hlen : ∀ (u : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
      (cache : (M × Commit →ₒ Chal).QueryCache) (D : List Commit)
      (z' : γ × DeferredReadState M Commit Chal),
      z' ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run
          ((((cache, sgn), D), bad), rl)) →
      (z'.2.2.length : ℝ≥0∞) ≤ ((rl.length + qH : ℕ) : ℝ≥0∞) := by
    intro u cache D z' hz'
    have := deferredDrawReadImpl_run_readlist_length_le ids M maxAttempts pk sk (ob u) qH
      (hob u) ((((cache, sgn), D), bad), rl) z' hz'
    exact_mod_cast this
  -- Per-`ws` value-substituted ungated head charge.
  set H : Commit × PrvState → ℝ≥0∞ := fun ws =>
    ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob rws.1.1)).run
              ((((rws.2, sgn), dr), bad), rl)] * ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞) with hH
  -- Per-`ws` recorded-length factor of the one-attempt body (RHS length factor minus the `+1`).
  set R : Commit × PrvState → ℝ≥0∞ := fun ws =>
    ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= alc | uniformSample Chal >>= fun ch =>
        ids.respond pk sk ws.2 ch >>= fun oz =>
          match oz with
          | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
          | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
              (ghostSignDrawBody ids M pk sk msg n).run re] *
        ((alc.1.2.length : ℕ) : ℝ≥0∞) with hR
  -- The per-`ws` head bound, summed over `ws` (gate dropped, value-substituted, `ε`-kernel).
  have hHead : (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * H ws) ≤ L₀ := by
    rw [hH]
    -- Per `(rws, z)` the inner `ws`-marginal of `z.count ws.1` is `≤ L₀`; the body and continuation
    -- have full mass, so the whole head expectation is `≤ L₀`.
    have hinner : ∀ (rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache)
        (z : γ × DeferredReadState M Commit Chal),
        z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob rws.1.1)).run
            ((((rws.2, sgn), dr), bad), rl)) →
        (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
          ≤ L₀ := by
      intro rws z hz
      calc (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
          ≤ ENNReal.ofReal ε * ((z.2.2.length : ℕ) : ℝ≥0∞) :=
            tsum_probOutput_commit_mul_count_le (ids.commit pk sk) z.2.2 ε (fun cm => hGuess cm)
        _ ≤ L₀ := by rw [hL₀]; gcongr; exact_mod_cast hlen rws.1.1 rws.2 dr z hz
    -- Rewrite the head as a single average over `(ws, rws, z)`, reorder, bound, and recombine.
    calc (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] *
                    ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
        = ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] *
                  (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
                    ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞)) := by
          -- Fully distribute the probability weights, reorder `ws` innermost, recombine.
          simp_rw [← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun rws => ?_
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun z => ?_
          refine tsum_congr fun ws => by ring
      _ ≤ ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] * L₀ := by
          refine ENNReal.tsum_le_tsum fun rws => ?_
          refine mul_le_mul' le_rfl ?_
          refine ENNReal.tsum_le_tsum fun z => ?_
          rcases eq_or_ne Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
              (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] 0 with hz | hz
          · rw [hz]; simp
          · gcongr
            exact hinner rws z ((mem_support_iff _ _).mpr hz)
      _ = L₀ * ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun rws => ?_
          rw [ENNReal.tsum_mul_right, ← mul_assoc, mul_comm _ L₀, mul_assoc]
      _ = L₀ := by
          have hone : (∑' rws : (Option (Commit × Resp) × List Commit) ×
              (M × Commit →ₒ Chal).QueryCache,
              Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)]) = 1 := by
            rw [← hbodyMass re]
            exact tsum_congr fun rws => by rw [hcontMass rws.1.1 rws.2 dr, mul_one]
          rw [hone, mul_one]
  -- The per-`ws` LHS inner bound: head + recursive (the inductive hypothesis).
  have h_ws : ∀ ws : Commit × PrvState,
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
              ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ H ws + L₀ * R ws := by
    intro ws
    -- Body-`n` expected `length + 1` (the reject-branch length factor; `+1` is the head commit).
    set Rr : ℝ≥0∞ :=
      ∑' rws : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= rws | (ghostSignDrawBody ids M pk sk msg n).run re] *
        ((rws.1.2.length + 1 : ℕ) : ℝ≥0∞) with hRr
    -- `R ws = Pr[reject ws] · Rr` (accept records length `0`; reject records `ws.1 :: rws`).
    have hR_eq : R ws = Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
        Rr := by
      rw [hR, probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_right]
      simp only []
      rw [tsum_probOutput_bind_mul]
      refine tsum_congr fun ch => ?_
      rw [tsum_probOutput_bind_mul]
      -- Per response `oz`: accept records length `0`; reject records `(ws.1 :: rws).length`.
      have h_oz : ∀ oz : Option Resp,
          (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (match oz with
              | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
              | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re :
              ProbComp ((Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache))] * ((alc.1.2.length : ℕ) : ℝ≥0∞))
            = (if oz = none then Rr else 0) := by
        intro oz
        cases oz with
        | some z => rw [if_neg (by simp), tsum_probOutput_pure_mul]; simp
        | none =>
            rw [if_pos rfl, hRr, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
            refine tsum_congr fun rws => ?_
            simp only [Function.comp]
            rw [tsum_probOutput_pure_mul]
            simp [List.length_cons]
      rw [tsum_eq_single (none : Option Resp) fun oz hoz => by
        rw [h_oz oz, if_neg hoz, mul_zero]]
      rw [h_oz none, if_pos rfl]; ring
    -- Peel the challenge `ch`. On *accept* the recorded list is empty (charge `0`); only the
    -- *reject* branch contributes, gated by `Pr[none | respond]`.
    rw [tsum_probOutput_bind_mul]
    -- Per-challenge: peel the response, then case on accept/reject.
    have h_ch : ∀ ch : Chal,
        (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
          ≤ Pr[= none | ids.respond pk sk ws.2 ch] * (H ws + L₀ * Rr) := by
      intro ch
      rw [tsum_probOutput_bind_mul]
      -- Per response `oz`: accept records nothing (charge `0`); reject = head + recursion.
      have h_oz : ∀ oz : Option Resp,
          (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (match oz with
              | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
              | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re :
              ProbComp ((Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache))] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                    ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                  ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
            ≤ (if oz = none then H ws + L₀ * Rr else 0) := by
        intro oz
        cases oz with
        | some z =>
            rw [if_neg (by simp), tsum_probOutput_pure_mul]
            simp
        | none =>
            rw [if_pos rfl, map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
            -- The reject branch: split the recorded count list `ws.1 :: rws.1.2` into head + tail.
            have hsplit : ∀ rws : (Option (Commit × Resp) × List Commit) ×
                (M × Commit →ₒ Chal).QueryCache,
                (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                  Pr[= alc | (pure ((rws.1.1, ws.1 :: rws.1.2), rws.2) :
                    ProbComp ((Option (Commit × Resp) × List Commit) ×
                      (M × Commit →ₒ Chal).QueryCache))] *
                    ∑' z : γ × DeferredReadState M Commit Chal,
                      Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                          (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                        ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
                  = (∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run ((((rws.2, sgn), dr), bad), rl)] *
                          ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
                    + ∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run
                            ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                          ((rws.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) := by
              intro rws
              rw [tsum_probOutput_pure_mul]
              simp only [List.map_cons, List.sum_cons, Nat.cast_add]
              rw [show dr ++ ws.1 :: rws.1.2 = (dr ++ [ws.1]) ++ rws.1.2 from by simp]
              rw [show (∑' z : γ × DeferredReadState M Commit Chal,
                    Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                        (ob rws.1.1)).run ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                      ((z.2.2.count ws.1 : ℝ≥0∞) +
                        ((rws.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞)))
                  = (∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run
                            ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                          ((z.2.2.count ws.1 : ℕ) : ℝ≥0∞))
                    + ∑' z : γ × DeferredReadState M Commit Chal,
                        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                            (ob rws.1.1)).run
                            ((((rws.2, sgn), (dr ++ [ws.1]) ++ rws.1.2), bad), rl)] *
                          ((rws.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞) from by
                rw [← ENNReal.tsum_add]; exact tsum_congr fun z => by rw [mul_add]]
              -- Head: value-substitute the drawn list from `(dr ++ [ws.1]) ++ rws.1.2` to `dr`.
              congr 1
              exact deferredDrawRead_run_count_dl_invariant ids M maxAttempts pk sk (ob rws.1.1)
                ws.1 rws.2 sgn rl ((dr ++ [ws.1]) ++ rws.1.2) bad dr bad
            -- Now `h_oz none` reduces to: `∑'rws Pr[rws]·(head + rec) ≤ H ws + L₀·Rr`.
            simp only [Function.comp]
            simp_rw [hsplit, mul_add]
            rw [ENNReal.tsum_add]
            -- The head sum *is* `H ws`; the recursive sum is bounded by the inductive hypothesis.
            refine add_le_add (le_of_eq ?_) ?_
            · rw [hH]
            · -- `dr ++ [ws.1]` form matches the inductive hypothesis at the extended prefix.
              rw [hRr]
              refine le_trans ?_ (ih re (dr ++ [ws.1]))
              exact le_of_eq (tsum_congr fun x => by rw [List.append_assoc])
      -- Sum over `oz`: only the reject (`none`) term survives, gated by `Pr[none | respond]`.
      calc (∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
              ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
                Pr[= alc | (match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re :
                  ProbComp ((Option (Commit × Resp) × List Commit) ×
                    (M × Commit →ₒ Chal).QueryCache))] *
                  ∑' z : γ × DeferredReadState M Commit Chal,
                    Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                        (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                      ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
          ≤ ∑' oz : Option Resp, Pr[= oz | ids.respond pk sk ws.2 ch] *
              (if oz = none then H ws + L₀ * Rr else 0) :=
            ENNReal.tsum_le_tsum fun oz => by gcongr; exact h_oz oz
        _ = Pr[= none | ids.respond pk sk ws.2 ch] * (H ws + L₀ * Rr) := by
            rw [tsum_eq_single (none : Option Resp) fun oz hoz => by rw [if_neg hoz, mul_zero]]
            rw [if_pos rfl]
    -- Sum over `ch`: factor out the reject probability and fold via `hR_eq`.
    calc (∑' ch : Chal, Pr[= ch | uniformSample Chal] *
            ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= alc | ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] *
                ∑' z : γ × DeferredReadState M Commit Chal,
                  Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                      (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                    ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ∑' ch : Chal, Pr[= ch | uniformSample Chal] *
            (Pr[= none | ids.respond pk sk ws.2 ch] * (H ws + L₀ * Rr)) :=
          ENNReal.tsum_le_tsum fun ch => by gcongr; exact h_ch ch
      _ = (∑' ch : Chal, Pr[= ch | uniformSample Chal] *
            Pr[= none | ids.respond pk sk ws.2 ch]) * (H ws + L₀ * Rr) := by
          rw [← ENNReal.tsum_mul_right]; exact tsum_congr fun ch => (mul_assoc _ _ _).symm
      _ = Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] *
            (H ws + L₀ * Rr) := by rw [probOutput_bind_eq_tsum]
      _ ≤ H ws + L₀ * R ws := by
          rw [mul_add, hR_eq]
          refine add_le_add (mul_le_of_le_one_left zero_le' probOutput_le_one) ?_
          rw [← mul_assoc, mul_comm
            Pr[= none | uniformSample Chal >>= fun ch => ids.respond pk sk ws.2 ch] L₀, mul_assoc]
  -- Assemble: unfold the `succ` body, peel the commit draw, apply `h_ws`, and split the sums.
  rw [run_ghostSignDrawBody_succ, tsum_probOutput_bind_mul]
  rw [tsum_probOutput_bind_mul]
  -- RHS inner equals `R ws + 1` (the body never fails, so the `+1` carries full mass).
  have hRinner : ∀ ws : Commit × PrvState,
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re] *
          ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞))
        = R ws + 1 := by
    intro ws
    have hmass : (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
        Pr[= alc | uniformSample Chal >>= fun ch =>
          ids.respond pk sk ws.2 ch >>= fun oz =>
            match oz with
            | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
            | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                (ghostSignDrawBody ids M pk sk msg n).run re]) = 1 :=
      tsum_probOutput_eq_one' (by simp)
    rw [hR]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | uniformSample Chal >>= fun ch =>
            ids.respond pk sk ws.2 ch >>= fun oz =>
              match oz with
              | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
              | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                  (ghostSignDrawBody ids M pk sk msg n).run re] *
            ((alc.1.2.length : ℝ≥0∞) + 1))
        = (∑' alc, Pr[= alc | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] * (alc.1.2.length : ℝ≥0∞))
          + ∑' alc, Pr[= alc | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] from by
      rw [← ENNReal.tsum_add]; exact tsum_congr fun alc => by rw [mul_add, mul_one]]
    rw [hmass]
  calc (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | uniformSample Chal >>= fun ch =>
              ids.respond pk sk ws.2 ch >>= fun oz =>
                match oz with
                | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                    (ghostSignDrawBody ids M pk sk msg n).run re] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob alc.1.1)).run ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                  ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (H ws + L₀ * R ws) :=
          ENNReal.tsum_le_tsum fun ws => by gcongr; exact h_ws ws
      _ = (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * H ws)
            + ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (L₀ * R ws) := by
          rw [← ENNReal.tsum_add]; exact tsum_congr fun ws => by rw [mul_add]
      _ ≤ L₀ + ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (L₀ * R ws) := by
          gcongr
      _ = L₀ * ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] *
            ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
              Pr[= alc | uniformSample Chal >>= fun ch =>
                ids.respond pk sk ws.2 ch >>= fun oz =>
                  match oz with
                  | some z => pure ((some (ws.1, z), []), re.cacheQuery (msg, ws.1) ch)
                  | none => (fun rws => ((rws.1.1, ws.1 :: rws.1.2), rws.2)) <$>
                      (ghostSignDrawBody ids M pk sk msg n).run re] *
                ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
          have hcommitMass : (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk]) = 1 :=
            tsum_probOutput_eq_one' (by simp)
          simp_rw [hRinner, mul_add, mul_one]
          rw [ENNReal.tsum_add, hcommitMass, mul_add, mul_one]
          rw [show (∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * (L₀ * R ws))
              = L₀ * ∑' ws : Commit × PrvState, Pr[= ws | ids.commit pk sk] * R ws from by
            rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun ws => by ring]
          rw [add_comm]

omit [SampleableType Stmt] in
/-- **The constant-length body charge (the genuine per-attempt induction).** Over one signing body
`ghostSignDrawBody n`, the expected continuation read-multiplicity of the body's *rejected* draws —
`E[Σ_{w ∈ body-rejects} continuation.readlist.count w]` — is at most `ε · (rl.length + qH) ·
E[#body-rejects + 1]`, where `rl` is the continuation's start read list and `qH` the continuation's
read-query budget (so the continuation's recorded read list has length `≤ rl.length + qH`
deterministically). The `+1` is the body's single unconditional signing query; it is *not* slack —
it pays the reject-gate skew of the head charge (see below).

Proved by induction on `n`:
* **0** — the body rejects nothing, the read-multiplicity is `0 ≤ ε · (rl.length + qH) · 1`.
* **n+1** — peel the head commit draw `ws` (kept *averaged*: the `ε`-kernel needs the full
  `ids.commit` marginal — a per-`ws` bound is false, the adversary could target a fixed `ws.1`),
  the challenge, the response, and case on the accept/reject branch. On *accept* the body records
  nothing (`rej = []`, charge `0`). On *reject* the recorded rejects are `ws.1 :: rec-rejects`; the
  read-multiplicity `Σ_{w ∈ ws.1 :: rec-rejects} z'.readlist.count w` splits as
  `z'.readlist.count ws.1` (head) plus the recursive body charge (recurses to the inductive
  hypothesis at the extended start drawn list `dr ++ [ws.1]`).

  Crucially the two halves treat the reject gate `1[respond = none]` differently:
  * the **head** charge `Σ_{ws} commit(ws) · 1[reject(ws.2)] · z'.readlist.count ws.1` drops the
    gate (`1[reject] ≤ 1`) — necessary because `ws.1` and the reject decision `f(ws.2, c)` are
    *correlated* (the prover state `ws.2` determines both the commit and the accept decision), so a
    gated kernel would skew the `ws.1` marginal. After value-substitution
    (`deferredDrawRead_run_sum_count_dl_invariant` moves `ws.1` out of the continuation's drawn
    list) and the marginal `ε`-kernel `tsum_probOutput_commit_mul_count_le`, the ungated head is
    `≤ ε · z'.readlist.length ≤ ε · (rl.length + qH)`, paid by the unconditional `+1`;
  * the **recursive** charge `Σ_{ws} commit(ws) · 1[reject(ws.2)] · (rec body charge)` *keeps* the
    gate, so it is `Pr[reject] · ε · (rl.length + qH) · E[#rec-rejects + 1]` (inductive hypothesis),
    which the reject paths of `#body-rejects` in the right-hand side exactly cover. Dropping the
    recursive gate would be unsound (it over-charges by the accept mass). -/
theorem ghostSignDrawBody_continuation_charge {γ : Type}
    (qH : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (msg : M)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hob : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (sgn : List M) (rl : List Commit) (bad : Bool) :
    ∀ (n : ℕ) (re : (M × Commit →ₒ Chal).QueryCache) (dr : List Commit),
      (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, sgn), dr ++ alc.1.2), bad), rl)] *
                ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((rl.length + qH : ℕ) : ℝ≥0∞) *
          ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg n).run re] *
              ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
  classical
  intro n
  induction n with
  | zero =>
      intro re dr
      simp only [ghostSignDrawBody, StateT.run_pure, tsum_probOutput_pure_mul, List.map_nil,
        List.sum_nil, Nat.cast_zero, mul_zero, tsum_zero]
      exact zero_le'
  | succ n ih =>
      intro re dr
      -- The genuine per-attempt step; see `ghostSignDrawBody_succ_charge`.
      exact ghostSignDrawBody_succ_charge ids M maxAttempts qH ε hε pk sk hGuess msg ob hob sgn rl
        bad n re dr ih


omit [SampleableType Stmt] in
/-- **The sign-step value-free charge (the isolated remaining core of the #228 ghost-read bound).**
This is the single-query step of the inline-run induction
`readRecord_expected_pairs_nontape_general` at a *signing* query `Sum.inr msg`. The signing body
`ghostSignDrawBody` draws `maxAttempts` fresh commitments inline, records the *rejected* ones into
the drawn list, and runs the continuation `ob` from the post-body state; the goal bounds the
resulting expected pair count by the `s`-based pre-existing term plus `ε` times the `s`-based
new-attempt count.

The genuine content is concentrated here. Expanding the inductive hypothesis at the post-body state,
the only term not covered by the `s`-based pre-existing term and the slack of the `#attempt` count
is the **body charge** `E[Σ_{rc ∈ readlist} body-rejects.count rc]`, which must be bounded by
`ε · E[readlist.length · #body-attempts]` (where `#body-attempts = #body-rejects + 1`, the body's
single unconditional signing query providing the `+1`). Crucially the body's draws must remain
**averaged** (the sum over body outputs is retained, not factored): for a *fixed* body output the
recorded rejected commitment is a determined value, and a continuation adversary could read the
random oracle at exactly that value, so the per-output charge is not `≤ ε`. The `ε` arises only by
averaging each rejected commitment over the fresh `ids.commit pk sk` draw
(`tsum_probOutput_commit_mul_count_le`).

The statement is **TRUE** (verified): the recorded read list is *value-free* — the continuation's
reads answer via `roStep` on the real layer and never the drawn (rejected) values, and the rejected
commitments are write-only (never cached; only accepted commitments are, via `cacheQuery`). The
value-substitution lemma `deferredDrawRead_run_count_dl_invariant` makes this precise: the
continuation's expected `readlist.count w` is invariant under the start drawn list, so the read list
is independent of every rejected draw's *value*. Combined with the body's draws being independent of
*reach* (a position is reached iff the earlier attempts rejected, which is determined by the earlier
draws — the body tape factorization `evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody` exhibits
this), each rejected draw charges its continuation read-multiplicity at the full marginal
`Pr[· | Prod.fst <$> commit] ≤ ε` (drop the reject indicator `≤ 1` on the value-substituted, hence
fixed, read list — no rejection-conditioning skew). The body's single unconditional signing query
(`+1`) pays the full-marginal head charge, and the read list `⊥` the attempt count factors
`E[readlist.length · #attempts] = E[readlist.length] · E[#attempts]`.

**Proof.** Unfold the sign step (`deferredDrawReadImpl … (Sum.inr msg)`), which maps each
signing-body output `alc` to the post-state with drawn list `s.drawn ++ alc.1.2` and signed list
`msg :: s.signed`. The continuation charge from the post-body state is bounded per `alc` by the
inductive hypothesis `ih`; its pre-existing drawn count splits via `List.count_append` into the
start drawn count (matched against the right-hand side) and the *body coincidence*
`E[Σ_{rc ∈ readlist} alc.1.2.count rc]`, which the bilinear count swap `sum_map_count_comm` recasts
as `E[Σ_{w ∈ alc.1.2} readlist.count w]` and `ghostSignDrawBody_continuation_charge` bounds by
`ε · (rl.length + qH) · E[#attempts + 1]`. The slack length factor recombines via the deterministic
prefix monotonicities `deferredDrawRead_run_drawn_prefix` / `deferredDrawRead_run_signed_prefix`:
the gap between the start slack and the post-body slack is exactly `alc.1.2.length + 1` (the body's
rejected draws plus the single signing query), which the body's `+1` term covers. The continuation
run's full mass (`deferredDrawRead_run_neverFail`) makes the constant-length factor `L₀` exact. -/
theorem nontape_signStep_charge {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (_hp₀ : 0 ≤ p_abort) (_hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (_hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (msg : M)
    (ob : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg) →
      OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (s : DeferredReadState M Commit Chal)
    (hob : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (ih : ∀ (u : ((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg))
        (s' : DeferredReadState M Commit Chal),
        (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH →
        (∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run s'] *
              ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
          ≤ (∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run s'] *
                ((z.2.2.map (fun rc => s'.1.1.2.count rc)).sum : ℝ≥0∞))
            + ENNReal.ofReal ε * ((s'.2.length + qH : ℕ) : ℝ≥0∞) *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob u)).run s'] *
                  (((z.2.1.1.2.length - s'.1.1.2.length)
                    + (z.2.1.1.1.2.length - s'.1.1.1.2.length) : ℕ) : ℝ≥0∞)) :
    (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        ((Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z |
                  (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
          + ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
            (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
              ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z |
                    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                  (((z.2.1.1.2.length - s.1.1.2.length)
                    + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞))) := by
  classical
  set L₀ : ℝ≥0∞ := ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) with hL₀
  -- Unfold the sign step: it maps each signing-body output `alc` to the post-state with drawn list
  -- `s.drawn ++ alc.1.2` and signed list `msg :: s.signed`. Convert all three sign-step averages to
  -- averages over the signing-body output `alc`.
  have hLHS : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞) :=
    tsum_probOutput_map_mul' _ _ _
  have hRHS1 : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
      = ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞) :=
    tsum_probOutput_map_mul' _ _ _
  have hRHS2 : (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        L₀ * (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞)))
      = L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                (((z.2.1.1.2.length - s.1.1.2.length)
                  + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.tsum_mul_left]; exact congrArg (L₀ * ·) (tsum_probOutput_map_mul' _ _ _)
  -- Rewrite all three sums to body averages; the RHS is `(pre-existing) + L₀ · (slack)`.
  rw [hLHS]
  rw [ENNReal.tsum_add]
  conv_rhs => rw [show (∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
          (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z |
                  (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
                (((z.2.1.1.2.length - s.1.1.2.length)
                  + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞)))
      = ∑' x : (((unifSpec + (M × Commit →ₒ Chal)) +
          (M →ₒ Option (Commit × Resp))).Range (Sum.inr msg)) × DeferredReadState M Commit Chal,
        L₀ * (Pr[= x | (deferredDrawReadImpl ids M maxAttempts pk sk (Sum.inr msg)).run s] *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z |
                (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob x.1)).run x.2] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞)) from
    tsum_congr fun x => by rw [hL₀]]
  rw [hRHS1, hRHS2]
  -- Both sides are now body averages; bound the LHS per `alc` by the inductive hypothesis at the
  -- post-body state, splitting the pre-existing drawn count and applying induction (1) to the body
  -- coincidence and the slack length identities.
  -- The body-coincidence charge `E_alc[E_z[Σ_{rc∈readlist} alc.1.2.count rc]]` is bounded by
  -- induction (1) (after the bilinear count swap `sum_map_count_comm`).
  have hbody : (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
              ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
            ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
      ≤ L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
    rw [hL₀]
    exact ghostSignDrawBody_continuation_charge ids M maxAttempts qH ε hε pk sk hGuess msg ob
      (fun u => hob u) (msg :: s.1.1.1.2) s.2 s.1.2 maxAttempts s.1.1.1.1 s.1.1.2
  -- The continuation runs never fail, so their mass is `1`.
  have hcontMass : ∀ alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
            ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)]) = 1 := fun alc =>
    tsum_probOutput_eq_one' (deferredDrawRead_run_neverFail ids M maxAttempts pk sk (ob alc.1.1) _)
  -- Per `alc`: split the pre-existing drawn count and rewrite the slack via the prefix lemmas.
  -- The slack inner sum splits as the post-body inductive slack plus the body's `#attempts + 1`.
  have hslack : ∀ (alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache),
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
            ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
          (((z.2.1.1.2.length - s.1.1.2.length)
            + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞))
      = (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
              ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
            (((z.2.1.1.2.length - (s.1.1.2 ++ alc.1.2).length)
              + (z.2.1.1.1.2.length - (msg :: s.1.1.1.2).length) : ℕ) : ℝ≥0∞))
        + ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) := by
    intro alc
    rw [show ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞)
        = (∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)]) *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞) from by rw [hcontMass alc, one_mul]]
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support ((simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
        (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2))
    · have hdr := deferredDrawRead_run_drawn_prefix ids M maxAttempts pk sk (ob alc.1.1)
        ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2) z hz
      have hsg := deferredDrawRead_run_signed_prefix ids M maxAttempts pk sk (ob alc.1.1)
        ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2) z hz
      simp only at hdr hsg
      rw [← mul_add]
      congr 1
      rw [← Nat.cast_add]
      congr 1
      simp only [List.length_append, List.length_cons] at hdr hsg ⊢
      omega
    · rw [probOutput_eq_zero_of_not_mem_support hz, zero_mul, zero_mul, zero_mul, add_zero]
  -- Per `alc`: the inductive hypothesis at the post-body state, with the pre-existing drawn count
  -- split into the start drawn count and the body coincidence (the bilinear count swap).
  have h_alc : ∀ (alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache),
      (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
            ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
              ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
            ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
        + (∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
              ((alc.1.2.map (fun w => z.2.2.count w)).sum : ℝ≥0∞))
          + L₀ * ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) (ob alc.1.1)).run
                  ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)] *
                (((z.2.1.1.2.length - (s.1.1.2 ++ alc.1.2).length)
                  + (z.2.1.1.1.2.length - (msg :: s.1.1.1.2).length) : ℕ) : ℝ≥0∞) := by
    intro alc
    have hih := ih alc.1.1 ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2), s.2)
      (hob alc.1.1)
    -- The post-state read list is `s.2`, so the read-length factor is `L₀`.
    simp only [hL₀.symm] at hih ⊢
    refine le_trans hih (le_of_eq ?_)
    congr 1
    -- Pre-existing drawn count `(s.drawn ++ alc.1.2).count` splits into `s.drawn.count` plus the
    -- body coincidence (via the bilinear count swap).
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    rw [← mul_add]
    congr 1
    rw [← Nat.cast_add]
    congr 1
    rw [show (z.2.2.map (fun rc => (s.1.1.2 ++ alc.1.2).count rc))
        = z.2.2.map (fun rc => s.1.1.2.count rc + alc.1.2.count rc) from
      List.map_congr_left fun rc _ => by rw [List.count_append]]
    rw [List.sum_map_add, sum_map_count_comm alc.1.2 z.2.2]
  -- Assemble: sum the per-`alc` bound, split into pre-existing + body-coincidence + ih-slack, then
  -- recombine the slack via `hslack` (the `#attempts + 1` gap) and the coincidence via `hbody`.
  refine le_trans (ENNReal.tsum_le_tsum fun alc => mul_le_mul' le_rfl (h_alc alc)) ?_
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, add_assoc]
  refine add_le_add le_rfl ?_
  -- The body coincidence plus the post-body inductive slack equal `L₀ · (the full RHS slack)`.
  have hslackSum :
      L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ((alc.1.2.length + 1 : ℕ) : ℝ≥0∞)
        + (∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
            Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
              (L₀ * ∑' z : γ × DeferredReadState M Commit Chal,
                Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                    (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                      s.2)] *
                  (((z.2.1.1.2.length - (s.1.1.2 ++ alc.1.2).length)
                    + (z.2.1.1.1.2.length - (msg :: s.1.1.1.2).length) : ℕ) : ℝ≥0∞)))
      = L₀ * ∑' alc : (Option (Commit × Resp) × List Commit) × (M × Commit →ₒ Chal).QueryCache,
          Pr[= alc | (ghostSignDrawBody ids M pk sk msg maxAttempts).run s.1.1.1.1] *
            ∑' z : γ × DeferredReadState M Commit Chal,
              Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk)
                  (ob alc.1.1)).run ((((alc.2, msg :: s.1.1.1.2), s.1.1.2 ++ alc.1.2), s.1.2),
                    s.2)] *
                (((z.2.1.1.2.length - s.1.1.2.length)
                  + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun alc => ?_
    rw [hslack alc, mul_add, add_comm]
    ring
  rw [← hslackSum]
  exact add_le_add hbody le_rfl

omit [SampleableType Stmt] in
/-- **The general per-pair charge over the inline read-recording run (induction carrier).** For an
arbitrary start state `s`, the expected pair count `E[Σ_{rc ∈ readlist} drawnlist.count rc]` is at
most the *un-charged pre-existing* contribution `E[Σ_{rc ∈ readlist} s.drawnlist.count rc]` (the
start drawn list, which the adversary may target deterministically) plus `ε` times the expected
`readlist.length · #new-attempts`, where `#new-attempts` counts only the draws and signing queries
made *after* `s` (the new drawn-list and signed-list growth). The base instance (empty start drawn
list) has a zero pre-existing term, giving `readRecord_expected_pairs_nontape_le`.

By induction on `oa`:
* **pure** — readlist and drawn list are the start ones; the pre-existing term *is* the pair count
  and there are no new attempts (equality).
* **read** — the drawn and signed lists are unchanged, so the bound passes through the inductive
  hypothesis (the bound never references the start *read* list, only the final one).
* **sign** — the body's fresh rejected draws extend the drawn list; the inductive hypothesis charges
  them as part of the continuation's pre-existing term, which splits as the genuine pre-existing
  term plus the body's contribution `E[Σ_{rc ∈ readlist} body-rejects.count rc]`, bounded by
  `ε · E[readlist.length · #body-rejects]` via the body-charge `nontape_signStep_body_charge` (the
  body's rejected values are independent of the value-free final read list); the residual `#new`
  attempt slack (`+1` per query) is absorbed. -/
theorem readRecord_expected_pairs_nontape_general {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hQ : oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (s : DeferredReadState M Commit Chal) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ (∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
            ((z.2.2.map (fun rc => s.1.1.2.count rc)).sum : ℝ≥0∞))
        + ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞) *
          ∑' z : γ × DeferredReadState M Commit Chal,
            Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run s] *
              (((z.2.1.1.2.length - s.1.1.2.length)
                + (z.2.1.1.1.2.length - s.1.1.1.2.length) : ℕ) : ℝ≥0∞) := by
  classical
  induction oa using OracleComp.inductionOn generalizing s qH with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
      simp only [add_zero, Nat.sub_eq_zero_of_le (le_refl _), Nat.cast_zero, mul_zero, add_zero]
      exact le_refl _
  | query_bind t ob ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul,
        ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      rcases t with (n | mc) | msg
      · -- UNIFORM: the step is deterministic in the state (`x.2 = s`); factor per step output and
        -- apply the inductive hypothesis directly (drawn / signed / read lists unchanged, budget
        -- unchanged: uniform queries are not read queries).
        have hQ2' : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH := by
          intro u; have := hQ2 u; simpa using this
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support ((deferredDrawReadImpl ids M maxAttempts pk sk
            (Sum.inl (Sum.inl n))).run s)
        · have hxs : x ∈ support ((fun u => (u, s)) <$>
              (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) n) := hx
          rw [support_map] at hxs
          obtain ⟨u, _, rfl⟩ := hxs
          beta_reduce
          rw [mul_left_comm (ENNReal.ofReal ε * ((s.2.length + qH : ℕ) : ℝ≥0∞)), ← mul_add]
          gcongr
          exact ih u qH (hQ2' u) s
        · rw [probOutput_eq_zero_of_not_mem_support hx]; simp
      · -- READ: the post-state drawn / signed lists are unchanged; the read list grows by one and
        -- the read budget decrements by one, so the constant `readlist.length + qH` is preserved.
        have hpos : 0 < qH := by
          rcases hQ1 with h | h
          · exact absurd rfl h
          · exact h
        have hQ2' : ∀ cu : Chal × (M × Commit →ₒ Chal).QueryCache,
            (ob cu.1).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) (qH - 1) := by
          intro cu; have := hQ2 cu.1; simpa using this
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support ((deferredDrawReadImpl ids M maxAttempts pk sk
            (Sum.inl (Sum.inr mc))).run s)
        · have hxs : x ∈ support ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache =>
              (cu.1, ((((cu.2, s.1.1.1.2), s.1.1.2), s.1.2 || decide (mc.2 ∈ s.1.1.2)),
                  mc.2 :: s.2))) <$> roStep M s.1.1.1.1 mc) := hx
          rw [support_map] at hxs
          obtain ⟨cu, _, rfl⟩ := hxs
          beta_reduce
          have hconst : ((s.2.length + qH : ℕ) : ℝ≥0∞)
              = (((mc.2 :: s.2).length + (qH - 1) : ℕ) : ℝ≥0∞) := by
            simp only [List.length_cons]; congr 1; omega
          rw [hconst, mul_left_comm (ENNReal.ofReal ε * (((mc.2 :: s.2).length + (qH - 1) : ℕ) :
            ℝ≥0∞)), ← mul_add]
          gcongr
          exact ih cu.1 (qH - 1) (hQ2' cu) ((((cu.2, s.1.1.1.2), s.1.1.2),
            s.1.2 || decide (mc.2 ∈ s.1.1.2)), mc.2 :: s.2)
        · rw [probOutput_eq_zero_of_not_mem_support hx]; simp
      · -- SIGN: the body's fresh rejected draws extend the drawn list; the body charge must keep
        -- the body draws *averaged* (a fixed body output lets the adversary target the recorded
        -- value), so the sum over body outputs is retained. The read budget is unchanged (signing
        -- is not a read query), so the continuation's `readlist.length` is bounded by the same
        -- constant `s.2.length + qH`. This is the value-free sign-step charge.
        have hQ2' : ∀ u, (ob u).IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH := by
          intro u; have := hQ2 u; simpa using this
        exact nontape_signStep_charge ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk hGuess
          hAbort msg ob s hQ2' (fun u s' hQ' => ih u qH hQ' s')

omit [SampleableType Stmt] in
/-- **The per-pair charge over the *inline* (non-tape) read-recording run.** Transporting the tape
target back through the fold equality `evalDist_deferredDrawRead_eq_drawList_tapeDrawRead` recasts
the expectation over the `deferredDrawReadImpl` run, where each rejected commitment is drawn
*inline* at its signing step rather than read from a front tape. In this representation each fresh
rejected
draw sits in the independent-of-the-readlist position required by the atomic value-free charge
`tsum_probOutput_commit_mul_count_le`: the recorded reads answer from `roStep` on the real layer and
never the drawn (rejected) values, so the final read list is independent of every rejected draw.

The charge is against `#attempts := drawnlist.length + (signedlist.length − l.length)`
(= #rejects + #signing-queries), whose mean is `qSrem/(1-p)`; the `drawnlist.length`-only form is
unsound (it omits the accepting attempts' fresh draws). The start drawn list is empty
(no pre-existing draws the adversary could target deterministically). -/
theorem readRecord_expected_pairs_nontape_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (hQ : oa.IsQueryBoundP (· matches Sum.inl (Sum.inr _)) qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, l), []), false), [])] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  -- Instantiate the general carrier at the empty-drawn-list start state: the pre-existing term
  -- vanishes (`[].count _ = 0`), the constant read-length factor `s.2.length + qH` becomes `qH`
  -- (empty start read list), and `#new-attempts` becomes the target `#attempts`.
  have hgen := readRecord_expected_pairs_nontape_general ids M maxAttempts qH ε p_abort hp₀ hp hε
    pk sk hGuess hAbort oa hQ ((((re, l), []), false), [])
  simp only [List.count_nil, List.map_const', List.sum_replicate, smul_zero, Nat.sub_zero,
    List.length_nil, Nat.cast_zero, mul_zero, tsum_zero, zero_add] at hgen
  exact hgen

omit [SampleableType Stmt] in
/-- **The per-position charge in the tape-factored representation (the isolated remaining core).**
After the fold-level tape factorization `evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`, the
read-recording run is `drawList (ids.commit pk sk) (maxAttempts·qSrem) >>= fun tape => …`, with the
draw tape sampled *upfront* as one independent block. In this representation the recorded drawn list
is a function of the tape (its rejected entries) while the recorded read list is **value-free** (the
reads answer from `roStep` on the real layer, never the tape values), so the read list is manifestly
independent of the tape values.

**The charge is against `#attempts`, not `drawnlist.length`.** The natural per-position bound takes
each *consumed* tape position (drop the reject check): `drawnlist.count rc ≤ #consumed positions k
with `tape[k].1 = rc``, and for a fixed position `tape[k]` is a fresh raw `Prod.fst <$> ids.commit`
draw of mass `≤ ε` (`hGuess`), independent of the value-free `rc` and of whether `k` is reached
(reach depends only on *earlier* tape entries). Summing gives `≤ ε · readlist.length · #consumed`.
The RHS therefore uses `#attempts := drawnlist.length + (signedlist.length − l.length)`
(= #rejects + #signing-queries `≥` #consumed), whose mean is the same `qSrem/(1-p)`
(`deferredDrawRead_attemptKn_mean_le`). The earlier `drawnlist.length`-form RHS is provably FALSE
(reject-conditioning / accept-undercounting: charging all consumed positions exceeds the
rejected-only count by the accepted positions, `ε · E[#accepts]`); this `#attempts` form is the
sound restatement and keeps the public `euf_cma` bound byte-identical (the consumer
`readRecord_expected_coincidences_le` uses `E[#attempts] ≤ qSrem/(1-p)`).

This is strictly better-isolated than the pre-transport atom: the tape is an explicit front variable
(no longer hidden inside the opaque `simulateQ (oa)` fold), so the tape⊥read-list independence is a
property of an explicit `bind` rather than the genuine multi-week joint coupling the fold-level
factorization (now banked) resolved.

**The sole remaining structural crux (sharpened: it is FUNCTIONAL, not distributional).** The
per-position charge reduces to one independence over `tapeDrawReadImpl`: the recorded read list is
independent of a *rejected* tape position's `Commit` value. The sharp form is a *support-level
value-substitution* fact, not a distributional conditional independence: the accept/reject decision
of `tapeSignBody` on the head `(w, st)` is `ids.respond pk sk st c = none`, which depends on the
`PrvState` part `st` and the challenge `c` but **not on the `Commit` part `w`**. Hence, for any
fixed state and challenge randomness, on a position the body *rejects*, replacing `tape[k].1 = w` by
any other `w'` leaves the output, the real cache, and (therefore, through the value-free `roStep`
read channel) the entire recorded read list unchanged — only the recorded drawn list changes (`w'`
instead of `w`). The accept branch returns `(some (w, z), [])` (so `w` enters the output/signature
there — the reason the reject indicator must be kept to exclude accepted positions); the reject
branch records `w` write-only into the drawn list. So the crux is a property of the explicit-tape
run's *support / dependence structure*, provable by a value-substitution argument rather than a
joint PMF×PMF coupling. Formalizing it still requires an inductive lemma over the `simulateQ (oa)`
fold carrying the invariant "the recorded read list does not depend on the `Commit` part of any
already-consumed-and-rejected tape position". -/
theorem readRecord_expected_pairs_tape_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
                (((((re, l), []), false), []), tape)] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
              (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                  (p.1, p.2.1)) <$>
                (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
                  (((((re, l), []), false), []), tape)] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  -- The remaining content is the per-position value-free charge over the explicit front tape. Two
  -- equivalent routes, both reducing to the SAME crux structural lemma (see the docstring):
  -- * drop-reject per-position: `Σ_{rc∈readlist} drawnlist.count rc =
  --   Σ_k 1[reached k]·1[rejects k]·readlist.count tape[k].1`; expand `tape[k]` by its i.i.d. `w`
  --   (`Pr[tape[k]=w] = commit w`); factor `reached-k ⊥ tape[k]` (reach depends only on `tape[<k]`)
  --   and `readlist ⊥ tape[k].1` GIVEN `k` rejects (THE CRUX — a rejected position's value is
  --   write-only, never enters a signature/read target); drop `1[w rejects] ≤ 1` AFTER factoring on
  --   the i.i.d. value `w`; then `Σ_w commit(w)·readlist.count w = Σ_{rc∈readlist} commit(rc) ≤
  --   |readlist|·ε`; finally `Σ_k E[1[reached k]·|readlist|·ε] = ε·E[|readlist|·#consumed] ≤
  --   ε·E[|readlist|·#attempts]`.
  -- * resampling equality: `(readlist, drawnlist) =d (readlist, fresh i.i.d. draws ⊥ readlist of
  --   the same length)`, after which the pair expectation is `Σ_pairs E[1[rc=d']] ≤
  --   ε·|readlist|·#rejects ≤ ε·|readlist|·#attempts` by independence + `hGuess`.
  -- Both routes need the crux independence `readlist ⊥ (rejected tape position's VALUE)` over
  -- `tapeDrawReadImpl`: the tape→readlist channel is ONLY via signatures (= ACCEPTED entries), so a
  -- rejected position's `Commit` value never enters any read target or query answer (reads answer
  -- via `roStep` on the real layer). This is the genuine independence the campaign isolated; it is
  -- NOT resolved by the (banked) fold-level tape factorization
  -- `evalDist_deferredDrawRead_eq_drawList_tapeDrawRead`, which only front-loaded the draws.
  -- Transport BACK to the non-tape run via the STEP B fold equality: every tape probability equals
  -- the corresponding non-tape `deferredDrawReadImpl` run probability. This makes the recorded
  -- draws *inline-fresh* (drawn at each sign step) rather than front-loaded, which is the position
  -- in which each rejected draw is independent of the (value-free) final read list.
  have hfold := evalDist_deferredDrawRead_eq_drawList_tapeDrawRead ids M maxAttempts pk sk oa qSrem
    hQ.1 ((((re, l), []), false), [])
  have hpr : ∀ z : γ × DeferredReadState M Commit Chal,
      Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
          (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
              (p.1, p.2.1)) <$>
            (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
              (((((re, l), []), false), []), tape)] =
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] :=
    fun z => by rw [probOutput_def, probOutput_def, ← hfold]
  simp only [hpr]
  exact readRecord_expected_pairs_nontape_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
    hGuess hAbort oa hQ.2 re l

omit [SampleableType Stmt] in
/-- **The value-free per-pair atom (the sole open core of the #228 ghost-read bound).** The expected
pair count — the expected number of coinciding `(recorded read-commit, recorded drawn commit)`
pairs, `E[Σ_{rc ∈ readlist} drawnlist.count rc]` — is at most `ε` times the expected
`readlist.length · drawnlist.length`.

This is the genuine probabilistic content, isolated to its cleanest form. It is the per-pair
value-free independence: for every `(read slot, draw slot)` pair, `E[1[rc = d]] ≤ ε`, because
* each recorded drawn commit `d` is a fresh i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw of mass
  `≤ ε` (`hGuess`), recorded write-only on rejected attempts (the accept branch records `[]`);
* the recorded read-commit list is **value-free** — the reads answer from the real RO layer via
  `roStep`, never the drawn values (`blindStepProj_map_ghostBlindImpl_indep` /
  `ghostHybridImpl_proj_trans`), so the readlist is jointly independent of the drawn *values*.

Summing the per-pair bound over the `readlist.length · drawnlist.length` pairs gives the claim. The
genuine difficulty (confirmed multi-week, see the campaign record) is that the factoring
`E[Σ_pairs 1[rc=d]] = Σ_pairs E[1[rc=d]]` with each factor `≤ ε` must be lifted through the opaque
adversary `simulateQ (oa)` fold: a draw-before-read pair has its draw resolved before the later
read, so the read-step increment is deterministic in the pre-state and is not `≤ ε` at that single
step. Bounding it needs the global factoring of the readlist law from the drawn-value law — the
fold-level value-free commute (`OracleComp.probEvent_bind_fire_eq_defer` lifted across all
interleaved attempts).

**Tape factorization (the banked per-body half).** The *body-level* half of that fold-lift is now
proved and axiom-clean: `evalDist_ghostSignDrawBody_eq_drawList_tapeSignBody` recasts one signing
body's inline attempt draws as consumption from a pre-drawn tape
(`𝒟[(ghostSignDrawBody … n).run re] = 𝒟[drawList (ids.commit pk sk) n >>= tapeSignBody … tape]`),
front-loading that body's commitment block as one independent `drawList` draw via the local i.i.d.
resampling commute `evalDist_bind_comm_probComp`. The remaining open content is to lift this
*across* the `simulateQ (oa)` fold: the per-query tape blocks of every interleaved signing query
must commute to the very front (a single independent draw block of `≤ maxAttempts · qSrem`
commitments) past the adaptive read points, so that the front draw block is independent of the
value-free recorded readlist. That fold-level `bind`-commutation is the genuine multi-week PMF×PMF
joint coupling; the front-loaded game is not the image of `oa` under any handler, so no inductive
(per-step) coupling produces it.

The surrounding reduction (`countP_mem_le_sum_count`, the deterministic readlist-length bound
`deferredDrawReadImpl_run_readlist_length_le`, the expected drawn-list length fold
`deferredDrawRead_run_expected_drawnlist_length_le`, and the final arithmetic) is fully proven and
axiom-clean. -/
theorem readRecord_expected_pairs_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
      ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal,
          Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
              ((((re, l), []), false), [])] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
  classical
  -- STEP C: transport both expectations through the fold-level tape factorization, so the recorded
  -- draws become a function of the front tape and the value-free read list becomes independent of
  -- the tape values.
  have hfold := evalDist_deferredDrawRead_eq_drawList_tapeDrawRead ids M maxAttempts pk sk oa qSrem
    hQ.1 ((((re, l), []), false), [])
  have hpr : ∀ z : γ × DeferredReadState M Commit Chal,
      Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
          ((((re, l), []), false), [])] =
        Pr[= z | OracleComp.drawList (ids.commit pk sk) (maxAttempts * qSrem) >>= fun tape =>
            (fun p : γ × (DeferredReadState M Commit Chal × List (Commit × PrvState)) =>
                (p.1, p.2.1)) <$>
              (simulateQ (tapeDrawReadImpl ids M maxAttempts pk sk) oa).run
                (((((re, l), []), false), []), tape)] :=
    fun z => by rw [probOutput_def, probOutput_def, hfold]
  simp only [hpr]
  -- The per-pair charge in the tape-factored representation: with `drawnlist = f(tape)` (recorded
  -- rejected tape entries) and `readlist` value-free (`roStep`), each `(read slot, draw slot)` pair
  -- charges at most `ε` by `hGuess` (each tape entry is a fresh raw `Prod.fst <$> ids.commit` draw
  -- of mass `≤ ε`, independent of the value-free read points).
  exact readRecord_expected_pairs_tape_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
    hGuess hAbort oa qSrem hQ re l

omit [SampleableType Stmt] in
/-- **The expected-coincidence-count bound (the numeric remaining obligation, first-moment route).**
The read-recording run's expected coincidence count
`E[#{ rc ∈ readlist : rc ∈ drawnlist }]` — the first moment fed by the banked Markov step
`readRecord_pred_le_expected_coincidences` — is at most `qSrem · (qH+1) · ε / (1-p)`.

This is the σ-free numeric form of the remaining open content (no front-loaded game, no all-miss
strategy `σ`): both the headline ghost-read bound and the `euf_cma` proof are charged through this
single numeric inequality.

**The accounting (why this is TRUE and additive — no per-output skew).** The coincidence count is a
double sum `Σ_{rc ∈ readlist} Σ_{d ∈ drawnlist} 1[rc = d]`, hence purely additive; the
rejection-conditioning skew that broke every `Pr[bad]` / per-output route lives in
output-conditioning, never in a SUM. Bounding `E[count]` decomposes over (read, draw) pairs:
* each recorded drawn commit `d` is a fresh i.i.d. raw `Prod.fst <$> ids.commit pk sk` draw of mass
  `≤ ε` (`hGuess`), recorded write-only on rejected attempts (the accept branch records `[]`);
* the recorded read-commit list is **value-free** — the reads answer from the real RO layer via
  `roStep`, never the drawn values (`blindStepProj_map_ghostBlindImpl_indep` /
  `ghostHybridImpl_proj_trans`), so the readlist is jointly independent of the drawn *values*;
* by that independence, for each pair `E[1[rc = d]] ≤ ε`, and there are `≤ (qH+1) · E[#attempts]`
  pairs (`(qH+1)` reads by `hQ`, `E[#attempts] ≤ qSrem/(1-p)` by `deferredDraw_attemptKn_mean_le`),
  giving `E[count] ≤ (qH+1) · ε · E[#attempts] ≤ qSrem · (qH+1) · ε / (1-p)`.

**The reduction (banked) and the sole open core.** The bound reduces by elementary arithmetic to a
single value-free atom (see the scaffolding lemmas above):
* the coincidence count is dominated pointwise by the pair count
  `Σ_{rc ∈ readlist} drawnlist.count rc` (`countP_mem_le_sum_count`);
* the recorded readlist has length `≤ qH` on the whole support — a *deterministic* bound from the
  read-query budget (`deferredDrawReadImpl_run_readlist_length_le`, empty start readlist);
* the expected drawn-list length is `≤ qSrem · (1/(1-p))` (`deferredDrawRead_run_expected_…`, empty
  start drawnlist);
* the genuine content is the **value-free per-pair atom** `readRecord_expected_pairs_le`:
  `E[Σ_{rc ∈ readlist} drawnlist.count rc] ≤ ε · E[readlist.length · drawnlist.length]`.

**The sole open core (the value-free fold-lift), isolated in `readRecord_expected_pairs_le`.** The
arithmetic after factoring the joint expectation is linear and discharged here; the factoring itself
— that each fresh draw is conditionally i.i.d. and `⊥` the recorded readlist *through the opaque
adversary `simulateQ (oa)` fold* — is the genuine PMF×PMF joint independence. A direct threaded fold
charges the *sign* steps cleanly (each fresh draw `⊥` the *current* readlist, value-free, additive),
but a *draw-before-read* pair has its draw resolved before the later read, so the read-step
increment `1[mc.2 ∈ drawnlist]` is deterministic in the pre-state and is not `≤ ε` at that single
step; bounding it needs the global factoring of the readlist law from the drawn-value law, which is
the same fold-level value-free commute as `OracleComp.probEvent_bind_fire_eq_defer` lifted across
all interleaved attempts.

The start drawn list is empty (`ws₀ = []`): the bound is sound only with no pre-existing draws,
since the adversary's read points are value-free w.r.t. the run's fresh draws but can
deterministically target a fixed pre-existing commitment. The headline instance uses the empty
start. -/
theorem readRecord_expected_coincidences_le {γ : Type}
    (qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit, Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))) γ)
    (qSrem : ℕ)
    (hQ : FiatShamir.signHashQueryBound M (S' := Option (Commit × Resp)) (oa := oa) qSrem qH)
    (re : (M × Commit →ₒ Chal).QueryCache) (l : List M) :
    (∑' z : γ × DeferredReadState M Commit Chal,
        Pr[= z | (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run
            ((((re, l), []), false), [])] *
          (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞))
      ≤ ENNReal.ofReal ((qSrem : ℝ) * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  classical
  obtain ⟨hQS, hQH⟩ := hQ
  set run : ProbComp (γ × DeferredReadState M Commit Chal) :=
    (simulateQ (deferredDrawReadImpl ids M maxAttempts pk sk) oa).run ((((re, l), []), false), [])
    with hrun
  -- Step 1+2: dominate the coincidence count pointwise by the pair count.
  have hstep12 :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          (z.2.2.countP (fun rc => decide (rc ∈ z.2.1.1.2)) : ℝ≥0∞))
        ≤ ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
            ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞) := by
    refine ENNReal.tsum_le_tsum fun z => ?_
    gcongr
    exact_mod_cast countP_mem_le_sum_count z.2.2 z.2.1.1.2
  -- Step 3 (the atom): the expected pair count is `≤ ε · qH · E[#attempts]`, where the read-list
  -- length is dominated *deterministically* by the read-query budget `qH` (the constant factor
  -- threaded through the carrier), and `#attempts := drawnlist.length + (signedlist.length −
  -- l.length)` (= #rejects + #queries). The `#attempts` (not `drawnlist.length = #rejects`) factor
  -- is the sound charge: charging per consumed tape position (drop-reject) covers all reached
  -- attempts, which dominates the rejected ones; its mean is the same `qSrem/(1-p)` as the drawn.
  have hatom :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.2.map (fun rc => z.2.1.1.2.count rc)).sum : ℝ≥0∞))
        ≤ ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
          ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
            ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) :
              ℝ≥0∞) := by
    rw [hrun]
    exact readRecord_expected_pairs_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
      hGuess hAbort oa qSrem ⟨hQS, hQH⟩ re l
  -- Step 5: `E[#attempts] ≤ qSrem · (1/(1-p))` (empty start drawnlist;
  -- `deferredDrawRead_attemptKn_mean_le`).
  have hdraw :
      (∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞))
        ≤ (qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort)) := by
    rw [hrun]
    exact deferredDrawRead_attemptKn_mean_le ids M maxAttempts pk sk hp₀ hp hAbort
      oa qSrem hQS re l
  -- Assemble the chain and convert to the target `ofReal` form. The exposed `(qH+1)` constant is
  -- the (loose) weakening of the deterministic read-length bound `qH`.
  refine le_trans hstep12 (le_trans hatom ?_)
  have hchain : ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
        ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
          ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)
      ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) * (qSrem : ℝ≥0∞) *
        ENNReal.ofReal (1 / (1 - p_abort)) := by
    calc ENNReal.ofReal ε * ((qH : ℕ) : ℝ≥0∞) *
            ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
              ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞)
        ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) *
            ∑' z : γ × DeferredReadState M Commit Chal, Pr[= z | run] *
              ((z.2.1.1.2.length + (z.2.1.1.1.2.length - l.length) : ℕ) : ℝ≥0∞) := by
          gcongr
          · exact le_self_add
      _ ≤ ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) *
            ((qSrem : ℝ≥0∞) * ENNReal.ofReal (1 / (1 - p_abort))) := by
          rw [mul_assoc, mul_assoc]
          gcongr
      _ = ENNReal.ofReal ε * ((qH : ℝ≥0∞) + 1) * (qSrem : ℝ≥0∞) *
            ENNReal.ofReal (1 / (1 - p_abort)) := by ring
  refine le_trans hchain (le_of_eq ?_)
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  rw [show ((qH : ℝ≥0∞) + 1) = ENNReal.ofReal ((qH : ℝ) + 1) by
        rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp,
      show ((qSrem : ℝ≥0∞)) = ENNReal.ofReal (qSrem : ℝ) by simp]
  rw [← ENNReal.ofReal_mul hε, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

omit [SampleableType Stmt] in
/-- **Ghost-blind ghost-read bound** (the sound headline target). The ghost-blind run's
adversarial-read bad mass is at most `qS·(qH+1)·ε/(1-p)`, via the first-moment route: the eager bad
mass is reduced to the deferred-draw run (`ghostBlind_bad_le_deferredDraw`), then to the
read-recording final-state read-hit predicate (`deferredDraw_bad_le_readRecord`), then to the
expected coincidence count by the banked Markov step (`readRecord_pred_le_expected_coincidences`),
which is finally charged by the numeric value-free bound `readRecord_expected_coincidences_le`.
Chaining with `probEvent_ghostHybridImpl_bad_le_ghostBlind` discharges the eager form
(`probEvent_ghostRead_bad_le`) without the unsound eager↔lazy detour. -/
theorem probEvent_ghostBlindImpl_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostBlindImpl ids M maxAttempts pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * ((qH : ℝ) + 1) * ε / (1 - p_abort)) := by
  -- The sound first-moment route: reduce the eager bad mass to the deferred-draw run (Piece A),
  -- then to the read-recording final-state predicate, then to the expected coincidence count (the
  -- banked Markov step), and charge that count by the numeric value-free bound.
  refine le_trans (ghostBlind_bad_le_deferredDraw ids M maxAttempts pk sk (adv.main pk)
    ((((∅, ∅), []), false) : GhostState M Commit Chal)
    ((((∅, []), []), false) : DeferredState M Commit Chal)
    ⟨rfl, rfl, fun mc h => absurd rfl h, by simp⟩) ?_
  refine le_trans (deferredDraw_bad_le_readRecord ids M maxAttempts pk sk (adv.main pk)
    ((((∅, []), []), false) : DeferredState M Commit Chal)
    (((((∅, []), []), false), []) : DeferredReadState M Commit Chal)
    ⟨rfl, fun h => absurd h (by simp)⟩) ?_
  refine le_trans (readRecord_pred_le_expected_coincidences ids M maxAttempts pk sk (adv.main pk)
    (((((∅, []), []), false), []) : DeferredReadState M Commit Chal)) ?_
  exact readRecord_expected_coincidences_le ids M maxAttempts qH ε p_abort hp₀ hp hε pk sk
    hGuess hAbort (adv.main pk) qS (hQ pk) ∅ []

omit [SampleableType Stmt] in
/-- **Ghost-read collision bound** for the Prog → Trans hop: the probability that the
adversary ever queries the random oracle at a ghost point (a rejected signing attempt's
programmed point) is at most `qS·(qH+1)·ε/(1-p)`.

Probabilistic content (deferred sampling): a rejected attempt's commitment `w` enters
the ghost layer with the joint law of `(w, c)` conditioned on rejection, and influences
the run only through the ghost-domain membership tests of later adversarial queries.
Per (rejected attempt `j`, adversarial query `k`) pair, the conditional independence of
the post-rejection run from `w` given the rejection event yields
`Pr[query k hits attempt j] ≤ Pr[attempt j runs] · ε` (the `1/Pr[reject]` skew of the
conditioned commitment law cancels against the rejection probability of the attempt).
Summing the expected number of attempts (`≤ 1/(1-p)` per signing query by `hAbort`)
against the `qH` adversarial queries (`hQ`) gives the bound; the budget `qH + 1` leaves
one unit of slack for a verification read, which the freshness check already rules out
(see `ghostHybridImpl_preserves_signed_inv`). Note that for `p_abort < 0` the
hypothesis `hAbort` forces rejection-free signing, so the ghost layer stays empty and
the left-hand side vanishes. -/
lemma probEvent_ghostRead_bad_le
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal => z.2.2 = true |
        (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk) (adv.main pk)).run
          ((((∅, ∅), []) :
            ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
              List M), false)]
      ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
  -- M1 reduces the eager ghost-read bad mass to the ghost-blind run's bad mass
  -- (`probEvent_ghostHybridImpl_bad_le_ghostBlind`, identical until bad), and the ghost-blind
  -- bound `probEvent_ghostBlindImpl_bad_le` (the first-moment route) closes it at
  -- `qS·(qH+1)·ε/(1-p)`. The residual `readRecord_expected_coincidences_le` carries the one
  -- open obligation; all downstream steps are banked axiom-clean.
  refine (probEvent_ghostHybridImpl_bad_le_ghostBlind ids hr M maxAttempts adv pk sk).trans ?_
  refine le_trans (probEvent_ghostBlindImpl_bad_le ids hr M maxAttempts adv qS qH ε p_abort
    hp₀ hp hε hQ pk sk hGuess hAbort) (le_of_eq ?_)
  norm_cast

/-! ## Hop lemmas

Each hop is stated per key pair, under pointwise hypotheses at that key; the good-key
event and `δ` enter only once, in the final averaging over `hr.gen`. -/

omit [SampleableType Stmt] in
/-- G₀ bridge: at every key pair produced by key generation, the real-signing hybrid
experiment reproduces the success probability of the standard unforgeability experiment
`SignatureAlg.unforgeableExp` under `runtime M`.

Distributional content: the runtime's `withStateOracle randomOracle` semantics of the
experiment (with its `WriterT` signing log) coincides with the single-cache-layer
presentation, with the `WriterT` log projected to the signed-message list. The proof is
a `simulateQ` commutation argument in the style of `roSim.run'_liftM_bind` and the
correctness proof in `FiatShamirWithAbort.correct`. -/
lemma probOutput_unforgeableExp_eq_hybridExpAtKey_real :
    Pr[= true | SignatureAlg.unforgeableExp (runtime M) adv] =
      Pr[= true | do
        let (pk, sk) ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (realSignBody ids M maxAttempts pk sk) pk] := by
  classical
  set base : QueryImpl (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) with hbase
  -- `base` matches the runtime's `withStateOracle` interpreter: both lift `unifSpec` by
  -- `liftTarget` (`unifFwdImpl` is exactly that) and use the caching `randomOracle`.
  have hrt : ∀ {α : Type} (oa : OracleComp (unifSpec + (M × Commit →ₒ Chal)) α),
      (runtime M).evalDist oa = 𝒟[(simulateQ base oa).run' ∅] := fun {α} oa => by
    rw [hbase]
    rfl
  unfold SignatureAlg.unforgeableExp
  rw [hrt]
  rw [show (FiatShamirWithAbort ids hr M maxAttempts).keygen =
    (liftM hr.gen : OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Stmt × Wit)) from rfl]
  rw [simulateQ_bind, roSim.run'_liftM_bind]
  refine probOutput_congr rfl ?_
  refine congrArg _ (bind_congr fun pksk => ?_)
  obtain ⟨pk, sk⟩ := pksk
  simp only []
  rw [hybridExpAtKey_eq_run_bind]
  -- Fuse the inner WriterT-logging `simulateQ` pass with the outer cache simulation
  -- `simulateQ base` via `writerTMapBase`, so the whole left-hand experiment becomes a
  -- single `simulateQ` over the run-normal-form cache base, still carrying the WriterT log.
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    QueryImpl.simulateQ_writerTMapBase_run]
  -- Remaining: reconcile the fused WriterT-log-over-`StateT cache` run with the hybrid's
  -- flat `StateT (cache × List M)` run. The bridge follows the Sigma-side recipe in
  -- `FiatShamir/Sigma/Stateful/Compatibility.lean`:
  --   1. `base.writerTMapBase implW = (toQueryImpl _).liftTarget _ + (realSignBody …).withLogging`
  --      (a per-query handler equality; the signing handler is `simulateQ base (sign …) =
  --      realSignBody`);
  --   2. `QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog` rewrites the WriterT log
  --      into a `StateT (List M)` input log carrying `[] ++ log.map fst`;
  --   3. `OracleComp.simulateQ_flattenStateT_run` flattens the nested `StateT (List M)
  --      (StateT cache ProbComp)` into the hybrid's flat `StateT (cache × List M) ProbComp`;
  --   4. a state-projection (`map_run_simulateQ_eq_of_query_map_eq`) matches the flattened
  --      handler against `hybridBaseImpl + hybridSignImpl realSignBody` (the lists differ only
  --      by append-vs-prepend ordering, which is invisible to the freshness check);
  --   5. the verify tail matches `hybridVerifyCont` with `wasQueried msg ↔ msg ∈ signed`
  --      via `QueryLog.wasQueried_eq_decide_mem_map_fst`.
  have hHandler : base.writerTMapBase
      ((HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))).liftTarget
          (WriterT (QueryLog (M →ₒ Option (Commit × Resp)))
            (OracleComp (unifSpec + (M × Commit →ₒ Chal)))) +
        (FiatShamirWithAbort (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
          ids hr M maxAttempts).signingOracle pk sk) =
      base.liftTarget
          (WriterT (QueryLog (M →ₒ Option (Commit × Resp)))
            (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) +
        QueryImpl.withLogging
          (fun msg => realSignBody ids M maxAttempts pk sk msg :
            QueryImpl (M →ₒ Option (Commit × Resp))
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) := by
    funext t
    rcases t with bq | sq
    · ext s
      simp [QueryImpl.writerTMapBase, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        HasQuery.toQueryImpl_apply, base, unifFwdImpl]
    · ext s
      simp [QueryImpl.writerTMapBase, QueryImpl.add_apply_inr, SignatureAlg.signingOracle,
        QueryImpl.withLogging_apply, FiatShamirWithAbort, realSignBody, base]
  rw [hHandler]
  -- Provide the cache base as a `HasQuery` instance so the WriterT-log → input-list replay
  -- lemma `QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog` matches
  -- `base.liftTarget _` (it equals `(HasQuery.toQueryImpl).liftTarget _` for this instance).
  letI hq : HasQuery (unifSpec + (M × Commit →ₒ Chal))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := base.toHasQuery
  -- Replay the WriterT log into a `StateT (List M)` input log, flatten the nested
  -- `StateT (List M) (StateT cache ProbComp)` to `StateT (List M × cache) ProbComp`, and
  -- match the flattened handler against `hybridBaseImpl + hybridSignImpl realSignBody` under
  -- the state swap `(List M × cache) → (cache × List M)`.
  set so : QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) :=
    (fun msg => realSignBody ids M maxAttempts pk sk msg) with hso
  -- (a) the WriterT-log run, mapped to `(out, log.map fst)`, equals the `appendInputLog` run.
  have hreplay := QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog
    (spec₀ := unifSpec + (M × Commit →ₒ Chal)) (loggedSpec := M →ₒ Option (Commit × Resp))
    (m₀ := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)
    so (adv.main pk) ([] : List M)
  simp only [] at hreplay
  -- The flattened `appendInputLog` handler.
  set implAppend : QueryImpl
      ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT (List M) (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) :=
    (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
      (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)).liftTarget
        (StateT (List M) (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) +
      QueryImpl.appendInputLog so with himplAppend
  -- (c) the flattened handler equals `hybridBaseImpl + hybridSignImpl realSignBody` after
  -- swapping the joint state `(List M × cache) → (cache × List M)`.
  -- `proj` swaps the components and reverses the list: the hybrid prepends each signed
  -- message (`msg :: l`) while `appendInputLog` appends it (`l ++ [msg]`), and reversing
  -- reconciles the two orderings step by step.
  set proj : List M × (M × Commit →ₒ Chal).QueryCache →
      (M × Commit →ₒ Chal).QueryCache × List M := fun s => (s.2, s.1.reverse) with hproj
  have hmatch : ∀ (t : ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))).Domain)
      (s : List M × (M × Commit →ₒ Chal).QueryCache),
      Prod.map id proj <$> (implAppend.flattenStateT t).run s =
        ((hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M so) t).run (proj s) := by
    rintro ((tu | tro) | tsign) ⟨l, c⟩
    · simp only [hproj, himplAppend, QueryImpl.flattenStateT, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply, hybridBaseImpl, unifFwdImpl]
      rfl
    · have hlhs : (implAppend.flattenStateT (Sum.inl (Sum.inr tro))).run (l, c) =
          roStep M c tro >>= fun a => pure (a.1, (l, a.2)) := by
        rw [himplAppend]
        simp only [QueryImpl.flattenStateT, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
          StateT.run_mk]
        erw [StateT.run_monadLift]
        have hbq : (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
            (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) (Sum.inr tro)).run c
            = roStep M c tro := randomOracle_run_eq_roStep M c tro
        rw [StateT.run_bind]
        erw [hbq]
        simp [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, monad_norm]
      rw [hlhs, hproj]
      simp only [QueryImpl.add_apply_inl]
      erw [hybridBaseImpl_run_ro]
      simp [map_eq_bind_pure_comp, bind_assoc, Function.comp]
    · have hlhs : (implAppend.flattenStateT (Sum.inr tsign)).run (l, c) =
          (so tsign).run c >>= fun a => pure (a.1, (l ++ [tsign], a.2)) := by
        simp [himplAppend, QueryImpl.flattenStateT, QueryImpl.add_apply_inr,
          QueryImpl.appendInputLog_apply, StateT.run_mk, StateT.run_bind, StateT.run_monadLift,
          StateT.run_modifyGet, modify, map_eq_bind_pure_comp, bind_assoc, Function.comp,
          monad_norm]
      rw [hlhs, hproj]
      simp only [QueryImpl.add_apply_inr]
      erw [hybridSignImpl_run]
      simp [map_eq_bind_pure_comp, bind_assoc, Function.comp, List.reverse_append]
  have hflat := fun {β : Type}
      (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
        (M →ₒ Option (Commit × Resp))) β) (s : List M × (M × Commit →ₒ Chal).QueryCache) =>
    OracleComp.map_run_simulateQ_eq_of_query_map_eq implAppend.flattenStateT
      (hybridBaseImpl (Commit := Commit) (Chal := Chal) M + hybridSignImpl M so)
      proj hmatch oa s
  -- Final assembly (steps b/d): chain `hreplay` (WriterT-log → `appendInputLog`),
  -- `OracleComp.simulateQ_flattenStateT_run` (flatten the nested `StateT (List M) (StateT cache)`
  -- to `StateT (List M × cache)`), and `hflat` (the `proj`-projection to the hybrid run on
  -- `(cache × List M)`), then identify the verify tail with `hybridVerifyCont` using
  -- `QueryLog.wasQueried_eq_decide_mem_map_fst` (`wasQueried msg ↔ msg ∈ log.map fst ↔
  -- msg ∈ (final signed list).reverse`, membership-invariant under the `proj` list reversal).
  -- (b) Apply `.run ∅` to `hreplay` (a `StateT cache` identity) to obtain a `ProbComp`
  -- identity for the cache-run of the WriterT log, with the log already projected to its
  -- list of queried messages.
  have hreplay' := congrArg
    (fun (g : StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp _) => g.run ∅) hreplay
  simp only [StateT.run_map] at hreplay'
  -- (c) Flatten the nested `StateT (List M) (StateT cache)` run into the joint-state run.
  have hflatten := OracleComp.simulateQ_flattenStateT_run implAppend (adv.main pk) ([] : List M)
    (∅ : (M × Commit →ₒ Chal).QueryCache)
  -- (d) Project the joint-state run onto the hybrid run via `proj`.
  have hflatHybrid := hflat (adv.main pk) (([], ∅) : List M × (M × Commit →ₒ Chal).QueryCache)
  rw [hproj] at hflatHybrid
  simp only [List.reverse_nil] at hflatHybrid
  -- Rewrite the hybrid run on the right as a pure relabelling of the cache-run of the
  -- WriterT-logged adversary, sending `(((msg, σ), log), cache)` to
  -- `((msg, σ), (cache, (log.map fst).reverse))`.
  rw [← hflatHybrid, hflatten, ← hreplay']
  simp only [map_bind, bind_assoc, map_pure, pure_bind, Prod.map, id]
  -- The cache base appearing in the left generator is exactly the `HasQuery.toQueryImpl`
  -- instance used by the replayed run (`hq := base.toHasQuery`).
  rw [show (HasQuery.toQueryImpl (spec := unifSpec + (M × Commit →ₒ Chal))
      (m := StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) = base from rfl]
  -- Push the relabelling map into the bind so both sides bind over the same generator.
  rw [bind_map_left]
  refine bind_congr fun p => ?_
  -- For each WriterT-run outcome `p = (((msg, σ), log), cache)`, the left verify tail equals
  -- `hybridVerifyCont` at the relabelled state `((msg, σ), (cache, (log.map fst).reverse))`.
  obtain ⟨⟨⟨msg, σ⟩, log⟩, cache⟩ := p
  simp only [hybridVerifyCont]
  rw [simulateQ_bind]
  simp only [simulateQ_pure, StateT.run_bind, StateT.run', map_bind, bind_map_left]
  refine bind_congr fun verified => ?_
  obtain ⟨ok, c⟩ := verified
  simp only [StateT.run_pure, map_pure, List.nil_append, List.mem_reverse,
    QueryLog.wasQueried_eq_decide_mem_map_fst, decide_not]
  -- Both sides are `!decide (msg ∈ log.map fst) && ok`; they differ only in the choice of
  -- `Decidable` instance for the membership test, which is a subsingleton, so `decide`
  -- agrees on the nose after normalising.
  norm_num [Bool.and_left_comm]

/-- Lift a cache-level hybrid handler to one carrying a never-touched bad flag in its
state, so the `expectedQuerySlack` bridge of `ProgramLogic/Relational/SimulateQ.lean`
applies. The flag is preserved on every step, hence stays `false` along any run started
from `false`. -/
noncomputable def flagLift {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl spec (StateT (σ × Bool) ProbComp) :=
  fun t => StateT.mk fun p =>
    (fun us : spec.Range t × σ => (us.1, (us.2, p.2))) <$> (impl t).run p.1

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
lemma flagLift_run {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) (t : spec.Domain) (s : σ) (b : Bool) :
    ((flagLift impl t).run (s, b)) =
      (fun us : spec.Range t × σ => (us.1, (us.2, b))) <$> (impl t).run s := rfl

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- Transport a predicate-targeted query bound across a (propositionally equal) choice of
predicate and `DecidablePred` instance. The predicate is allowed to differ by its match
auxiliary (which arises when the same matches-notation is elaborated in different
modules), and the decidability instance is a subsingleton. -/
lemma isQueryBoundP_cast_pred {ι : Type} {spec : OracleSpec ι} {α : Type}
    {oa : OracleComp spec α} {p₁ p₂ : spec.Domain → Prop}
    {i₁ : DecidablePred p₁} {i₂ : DecidablePred p₂} {n : ℕ} (hp : p₁ = p₂)
    (h : @OracleComp.IsQueryBoundP _ spec α oa p₁ i₁ n) :
    @OracleComp.IsQueryBoundP _ spec α oa p₂ i₂ n := by
  subst hp
  convert h using 2

/-- Arithmetic kernel of the Sign → Prog charge: the discrete first moment of a truncated
geometric series is dominated by the square of its zeroth moment, `∑_{a<m} a·pᵃ ≤
(∑_{a<m} pᵃ)²`. The right-hand convolution `(∑ pᵃ)² = ∑_{i,j} p^{i+j}` collects, for each
`k`, the `k+1` ordered pairs summing to `k`; injecting `(i, j) ↦ (i-j-1, j+1)` exhibits the
left sum as a subset of those nonnegative contributions. -/
lemma sum_natCast_mul_pow_le_sq_sum_pow (p : ℝ) (hp0 : 0 ≤ p) (m : ℕ) :
    ∑ a ∈ Finset.range m, (a : ℝ) * p ^ a ≤ (∑ a ∈ Finset.range m, p ^ a) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  set P := Finset.range m ×ˢ Finset.range m with hP
  set Q := (Finset.range m).sigma (fun i => Finset.range i) with hQ
  have hLHS : ∑ a ∈ Finset.range m, (a : ℝ) * p ^ a = ∑ q ∈ Q, p ^ q.1 := by
    rw [hQ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hLHS, show (∑ a ∈ P, p ^ a.1 * p ^ a.2) = ∑ a ∈ P, p ^ (a.1 + a.2) from
    Finset.sum_congr rfl fun a _ => by rw [pow_add]]
  have himg : ∑ q ∈ Q, p ^ q.1
      = ∑ r ∈ Q.image (fun q => (q.1 - (q.2 + 1), q.2 + 1)), p ^ (r.1 + r.2) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [hQ, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hq
      congr 1
      omega
    · intro a ha b hb hab
      rw [Finset.mem_coe, hQ, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at ha hb
      simp only [Prod.mk.injEq] at hab
      obtain ⟨h1, h2⟩ := hab
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only at *
      have hsnd : a2 = b2 := by omega
      subst hsnd
      have hfst : a1 = b1 := by omega
      subst hfst
      rfl
  rw [himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun r _ _ => by positivity)
  intro r hr
  rw [Finset.mem_image] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  rw [hQ, Finset.mem_sigma, Finset.mem_range, Finset.mem_range] at hq
  rw [hP, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  omega

omit [SampleableType Stmt] in
/-- Hop G₀ → G₁ (Sign → Prog) at a fixed key: replacing the caching hash of each signing
attempt by overwrite-reprogramming with a fresh challenge costs at most

`qS·ε·((qS+1)/(2·(1-p)²) + (qH+1)/(1-p))`.

Distributional content (identical-until-bad): the two games agree unless some signing
attempt commits to a point `(msg, w)` already present in the cache. Conditioned on good
keys, each attempt's commitment is `ε`-guessable (`hGuess`), the cache holds at most
`qH + 1` adversarial entries plus the entries of previous signing attempts, and the
expected number of attempts per signing query is at most `1/(1-p)` (`hAbort`, via
`sign_expectedQueries_le_geometric`). Intended vehicle:
`tvDist_simulateQ_le_probEvent_bad` (the fundamental lemma in
`ProgramLogic/Relational/SimulateQ.lean`) with the bad event tracked on the hybrid
state, plus the expected-attempt-count machinery of `WithAbort/ExpectedCost.lean`.

The nonnegativity hypothesis `hp₀` is necessary: for `p_abort < 0` the claimed loss
shrinks below the genuine adversarial-collision gap `qS·qH·ε` of an abort-free scheme
(the `1/(1-p)` factors fall below `1`), so the statement would be false. The
corresponding bound is available at every call site from the good-key event. -/
lemma probOutput_hybridExpAtKey_real_le_prog
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (realSignBody ids M maxAttempts pk sk) pk] ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (progSignBody ids M pk sk · maxAttempts) pk] +
        ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
          qS * (qH + 1) * ε / (1 - p_abort)) := by
  classical
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  set σ := (M × Commit →ₒ Chal).QueryCache × List M with hσ
  -- The combined cache-level handlers for the two games.
  set implReal : QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT σ ProbComp) :=
    hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
      hybridSignImpl M (realSignBody ids M maxAttempts pk sk) with himplReal
  set implProg : QueryImpl ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (StateT σ ProbComp) :=
    hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
      hybridSignImpl M (progSignBody ids M pk sk · maxAttempts) with himplProg
  set R : σ → ℝ≥0∞ := fun s => QueryCache.enncard s.1 with hR
  set ζ : ℝ≥0∞ := ENNReal.ofReal ε *
    ∑ a ∈ Finset.range maxAttempts, (a : ℝ≥0∞) * ENNReal.ofReal p_abort ^ a with hζ
  set β : ℝ≥0∞ := ENNReal.ofReal ε *
    ∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a with hβ
  set g : ℝ≥0∞ := ∑ a ∈ Finset.range maxAttempts, ENNReal.ofReal p_abort ^ a with hg
  set querySlack : σ → ℝ≥0∞ := fun s => ζ + R s * β with hquerySlack
  -- The per-charged-query TV slack: real-vs-prog within a single signing query.
  have h_step_tv_charged : ∀ (t : _), (· matches .inr _) t → ∀ (s : σ),
      ENNReal.ofReal (tvDist ((flagLift implProg t).run (s, false))
          ((flagLift implReal t).run (s, false))) ≤ querySlack s := by
    rintro (t' | msg) hc s
    · exact absurd hc (by simp)
    rcases s with ⟨c, l⟩
    -- Both flag-lifted signing runs are a single (shared, injective) map over the
    -- corresponding cache-level signing body; the map drops out of the TV distance,
    -- and the body-level TV is the proven `signCollisionBound`.
    have hrunProg : (flagLift implProg (Sum.inr msg)).run ((c, l), false) =
        (fun x : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
          (x.1, ((x.2, msg :: l), false))) <$>
            (progSignBody ids M pk sk msg maxAttempts).run c := by
      rw [flagLift_run, himplProg, QueryImpl.add_apply_inr]
      change (fun us => (us.1, us.2, false)) <$>
          ((fun ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
            (ac.1, (ac.2, msg :: l))) <$> (progSignBody ids M pk sk msg maxAttempts).run c) = _
      rw [Functor.map_map]
    have hrunReal : (flagLift implReal (Sum.inr msg)).run ((c, l), false) =
        (fun x : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
          (x.1, ((x.2, msg :: l), false))) <$>
            (realSignBody ids M maxAttempts pk sk msg).run c := by
      rw [flagLift_run, himplReal, QueryImpl.add_apply_inr]
      change (fun us => (us.1, us.2, false)) <$>
          ((fun ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
            (ac.1, (ac.2, msg :: l))) <$> (realSignBody ids M maxAttempts pk sk msg).run c) = _
      rw [Functor.map_map]
    rw [hrunProg, hrunReal]
    refine le_trans (ENNReal.ofReal_le_ofReal
      (le_trans (tvDist_map_le _ _ _) (le_of_eq (tvDist_comm _ _)))) ?_
    refine le_trans (ofReal_tvDist_run_fsAbortSignLoop_progSignBody_le
      ids M pk sk msg hGuess hAbort maxAttempts c) ?_
    rw [signCollisionBound_eq, hquerySlack, hζ, hβ, hR]
  -- Uncharged (base) queries: the two handlers coincide.
  have h_step_eq_uncharged : ∀ (t : _), ¬ (· matches .inr _) t → ∀ (p : σ × Bool),
      (flagLift implProg t).run p = (flagLift implReal t).run p := by
    rintro (t' | msg) hnc p
    · rw [flagLift_run, flagLift_run, himplProg, himplReal,
        QueryImpl.add_apply_inl, QueryImpl.add_apply_inl]
    · exact absurd rfl hnc
  -- The flag is never set: monotonicity is vacuous-by-preservation.
  have h_mono₁ : ∀ (t : _) (p : σ × Bool), p.2 = true →
      ∀ z ∈ support ((flagLift implProg t).run p), z.2.2 = true := by
    intro t p hp2 z hz
    rw [flagLift_run, support_map] at hz
    obtain ⟨us, -, rfl⟩ := hz
    exact hp2
  -- Expected-resource hypotheses for `expectedQuerySlack_expected_resource_le`.
  have h_charged : ∀ (t : _) (p : σ × Bool), p.2 = false → (· matches .inr _) t →
      ∑' z : _ × σ × Bool, Pr[= z | (flagLift implProg t).run p] * R z.2.1 ≤ R p.1 + g := by
    rintro (t' | msg) p - hc
    · exact absurd hc (by simp)
    rcases p with ⟨⟨c, l⟩, b⟩
    -- Reduce the flag-lifted signing run to the `progSignBody` cache-growth tsum.
    -- The combined-spec `Range (Sum.inr msg)` index of the tsum is only defeq (not
    -- syntactically equal) to `Option (Commit × Resp)`, so we `change` into the
    -- explicit type and rewrite the run as a single map over `progSignBody`.
    have hrun : (flagLift implProg (Sum.inr msg)).run ((c, l), b) =
        (fun x : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
          (x.1, ((x.2, msg :: l), b))) <$>
            (progSignBody ids M pk sk msg maxAttempts).run c := by
      rw [flagLift_run, himplProg, QueryImpl.add_apply_inr]
      change (fun us => (us.1, us.2, b)) <$>
          ((fun ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
            (ac.1, (ac.2, msg :: l))) <$> (progSignBody ids M pk sk msg maxAttempts).run c) = _
      rw [Functor.map_map]
    rw [hrun]
    change (∑' z : Option (Commit × Resp) × σ × Bool,
      Pr[= z | (fun x : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache =>
        (x.1, ((x.2, msg :: l), b))) <$>
          (progSignBody ids M pk sk msg maxAttempts).run c] * R z.2.1) ≤ _
    rw [map_eq_bind_pure_comp, tsum_probOutput_bind_mul]
    simp only [Function.comp, tsum_probOutput_pure_mul]
    exact tsum_probOutput_run_progSignBody_mul_enncard_le ids M pk sk msg hAbort maxAttempts c
  have h_growth : ∀ (t : _) (p : σ × Bool), p.2 = false →
      ¬ (· matches .inr _) t → (· matches .inl (.inr _)) t →
      ∀ z ∈ support ((flagLift implProg t).run p), R z.2.1 ≤ R p.1 + 1 := by
    rintro ((n | mc) | msg) p - hnc hg z hz
    · exact absurd hg (by simp)
    · rcases p with ⟨⟨c, l⟩, b⟩
      rw [flagLift_run, himplProg, QueryImpl.add_apply_inl] at hz
      replace hz : z ∈ support ((fun us : Chal × σ => (us.1, (us.2, b))) <$>
          ((fun cu : Chal × (M × Commit →ₒ Chal).QueryCache => (cu.1, (cu.2, l))) <$>
            roStep M c mc)) := by
        rw [← hybridBaseImpl_run_ro]; exact hz
      simp only [support_map] at hz
      obtain ⟨cu', ⟨cu'', hcu'', rfl⟩, rfl⟩ := hz
      -- The random-oracle step grows the cache by at most one entry.
      simp only [hR]
      rcases hmc : c mc with _ | v
      · rw [roStep_of_none M hmc] at hcu''
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hcu''
        obtain ⟨ch, -, rfl⟩ := hcu''
        exact QueryCache.enncard_cacheQuery_le c mc ch
      · rw [roStep_of_some M hmc] at hcu''
        rw [(by simpa using hcu'' : cu'' = (v, c))]
        exact le_self_add
    · exact absurd hg (by simp)
  have h_free : ∀ (t : _) (p : σ × Bool), p.2 = false →
      ¬ (· matches .inr _) t → ¬ (· matches .inl (.inr _)) t →
      ∀ z ∈ support ((flagLift implProg t).run p), R z.2.1 ≤ R p.1 := by
    rintro ((n | mc) | msg) p - hnc hng z hz
    · -- Uniform query: forwarded without touching the cache.
      rcases p with ⟨⟨c, l⟩, b⟩
      have hrun : (hybridBaseImpl (Commit := Commit) (Chal := Chal) M (.inl n)).run
          (c, l) = (fun x => (x, (c, l))) <$>
            (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)) := by
        simp only [hybridBaseImpl, QueryImpl.add_apply_inl]
        rfl
      rw [flagLift_run, himplProg, QueryImpl.add_apply_inl] at hz
      replace hz : z ∈ support ((fun us : unifSpec.Range n × σ => (us.1, (us.2, b))) <$>
          ((fun x : unifSpec.Range n => (x, ((c, l) : σ))) <$>
            (liftM (unifSpec.query n) : ProbComp (unifSpec.Range n)))) := by
        rw [← hrun]; exact hz
      simp only [support_map] at hz
      obtain ⟨x, ⟨y, -, rfl⟩, rfl⟩ := hz
      exact le_rfl
    · exact absurd rfl hng
    · exact absurd rfl hnc
  -- The bridge: run-level TV ≤ accumulated slack + Pr[bad].
  open OracleComp.ProgramLogic.Relational in
  have h_bridge :
      ENNReal.ofReal (tvDist
          ((simulateQ (flagLift implProg) (adv.main pk)).run ((∅, []), false))
          ((simulateQ (flagLift implReal) (adv.main pk)).run ((∅, []), false)))
        ≤ expectedQuerySlack (flagLift implProg)
            (· matches .inr _) querySlack (adv.main pk) qS (((∅, []) : σ), false)
          + Pr[fun z : _ × σ × Bool => z.2.2 = true |
              (simulateQ (flagLift implProg) (adv.main pk)).run (((∅, []) : σ), false)] := by
    refine ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad
      (flagLift implProg) (flagLift implReal) (· matches .inr _) querySlack
      h_step_tv_charged h_step_eq_uncharged h_mono₁ (adv.main pk)
      (queryBudget := qS) ?_ (((∅, []) : σ), false)
    exact isQueryBoundP_cast_pred (by funext x; rcases x with (_ | _) | _ <;> rfl) (hQ pk).1
  -- The bad-flag probability vanishes: the flag is preserved from `false`.
  have h_bad_zero : Pr[fun z : _ × σ × Bool => z.2.2 = true |
      (simulateQ (flagLift implProg) (adv.main pk)).run (((∅, []) : σ), false)] = 0 := by
    refine probEvent_eq_zero fun z hz hbad => ?_
    have hinv : ∀ y ∈ support ((simulateQ (flagLift implProg) (adv.main pk)).run
        (((∅, []) : σ), false)), y.2.2 = false := by
      refine OracleComp.simulateQ_run_preserves_inv_of_query (flagLift implProg)
        (fun s : σ × Bool => s.2 = false) (fun t s hs y hy => ?_) (adv.main pk)
        (((∅, []) : σ), false) rfl
      rw [flagLift_run, support_map] at hy
      obtain ⟨us, -, rfl⟩ := hy
      exact hs
    rw [hinv z hz] at hbad
    exact absurd hbad (by decide)
  -- The accumulated slack is bounded by the resource estimate.
  have h_slack_le : OracleComp.ProgramLogic.Relational.expectedQuerySlack (flagLift implProg)
        (· matches .inr _) querySlack (adv.main pk) qS (((∅, []) : σ), false)
      ≤ (qS : ℝ≥0∞) * ζ +
          ((qS : ℝ≥0∞) * R ((∅, []) : σ) + (qS : ℝ≥0∞) * (qH : ℝ≥0∞)
            + (qS.choose 2 : ℝ≥0∞) * g) * β := by
    refine OracleComp.ProgramLogic.Relational.expectedQuerySlack_expected_resource_le
      (flagLift implProg) (· matches .inr _) (· matches .inl (.inr _)) R ζ β g
      h_charged h_growth h_free (adv.main pk) (qS := qS) (qH := qH) ?_ ?_ ((∅, []) : σ)
    · exact isQueryBoundP_cast_pred (by funext x; rcases x with (_ | _) | _ <;> rfl) (hQ pk).1
    · exact isQueryBoundP_cast_pred (by funext x; rcases x with (_ | _) | _ <;> rfl) (hQ pk).2
  -- The flag-lifted run TV is bounded by the accumulated slack (the bad term vanishes).
  set slack : ℝ≥0∞ := (qS : ℝ≥0∞) * ζ +
      ((qS : ℝ≥0∞) * R ((∅, []) : σ) + (qS : ℝ≥0∞) * (qH : ℝ≥0∞)
        + (qS.choose 2 : ℝ≥0∞) * g) * β with hslack
  have h_flag_tv : ENNReal.ofReal (tvDist
      ((simulateQ (flagLift implProg) (adv.main pk)).run ((∅, []), false))
      ((simulateQ (flagLift implReal) (adv.main pk)).run ((∅, []), false))) ≤ slack := by
    refine le_trans h_bridge ?_
    rw [h_bad_zero, add_zero]
    exact h_slack_le
  -- Project the flag away: the flag-lifted runs map onto the (unflagged) hybrid runs.
  have hprojP : ∀ (t : _) (sb : σ × Bool),
      Prod.map id (Prod.fst : σ × Bool → σ) <$> (flagLift implProg t).run sb =
        (implProg t).run sb.1 := by
    intro t sb
    rw [flagLift_run, Functor.map_map]
    simp only [Prod.map, id_eq, Prod.mk.eta, id_map']
  have hprojR : ∀ (t : _) (sb : σ × Bool),
      Prod.map id (Prod.fst : σ × Bool → σ) <$> (flagLift implReal t).run sb =
        (implReal t).run sb.1 := by
    intro t sb
    rw [flagLift_run, Functor.map_map]
    simp only [Prod.map, id_eq, Prod.mk.eta, id_map']
  have hrunProj_P : (simulateQ implProg (adv.main pk)).run (∅, []) =
      Prod.map id (Prod.fst : σ × Bool → σ) <$>
        (simulateQ (flagLift implProg) (adv.main pk)).run ((∅, []), false) :=
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq (flagLift implProg) implProg
      (Prod.fst : σ × Bool → σ) hprojP (adv.main pk) ((∅, []), false)).symm
  have hrunProj_R : (simulateQ implReal (adv.main pk)).run (∅, []) =
      Prod.map id (Prod.fst : σ × Bool → σ) <$>
        (simulateQ (flagLift implReal) (adv.main pk)).run ((∅, []), false) :=
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq (flagLift implReal) implReal
      (Prod.fst : σ × Bool → σ) hprojR (adv.main pk) ((∅, []), false)).symm
  -- Hence the unflagged run TV is also bounded by the slack.
  have h_run_tv : ENNReal.ofReal (tvDist
      ((simulateQ implProg (adv.main pk)).run (∅, []))
      ((simulateQ implReal (adv.main pk)).run (∅, []))) ≤ slack := by
    rw [hrunProj_P, hrunProj_R]
    exact le_trans (ENNReal.ofReal_le_ofReal (tvDist_map_le _ _ _)) h_flag_tv
  -- Lift the run-level bound to the games through the shared verification continuation.
  have h_games_tv : ENNReal.ofReal (tvDist
      (hybridExpAtKey ids hr M maxAttempts adv (realSignBody ids M maxAttempts pk sk) pk)
      (hybridExpAtKey ids hr M maxAttempts adv
        (progSignBody ids M pk sk · maxAttempts) pk)) ≤ slack := by
    rw [hybridExpAtKey_eq_run_bind, hybridExpAtKey_eq_run_bind, tvDist_comm]
    refine le_trans (ENNReal.ofReal_le_ofReal (tvDist_bind_right_le _ _ _)) ?_
    rw [← himplProg, ← himplReal]
    exact h_run_tv
  -- Convert the game-level TV bound into the probability-output inequality.
  have h_prob : Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (realSignBody ids M maxAttempts pk sk) pk] ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (progSignBody ids M pk sk · maxAttempts) pk] + slack := by
    have habs := abs_probOutput_toReal_sub_le_tvDist
      (hybridExpAtKey ids hr M maxAttempts adv (realSignBody ids M maxAttempts pk sk) pk)
      (hybridExpAtKey ids hr M maxAttempts adv (progSignBody ids M pk sk · maxAttempts) pk)
    have h2 := (abs_le.mp habs).2
    calc Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (realSignBody ids M maxAttempts pk sk) pk]
        = ENNReal.ofReal (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts pk sk) pk].toReal) :=
          (ENNReal.ofReal_toReal probOutput_ne_top).symm
      _ ≤ ENNReal.ofReal (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (progSignBody ids M pk sk · maxAttempts) pk].toReal +
          tvDist (hybridExpAtKey ids hr M maxAttempts adv
              (realSignBody ids M maxAttempts pk sk) pk)
            (hybridExpAtKey ids hr M maxAttempts adv
              (progSignBody ids M pk sk · maxAttempts) pk)) := by
            refine ENNReal.ofReal_le_ofReal ?_; linarith [h2]
      _ = Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (progSignBody ids M pk sk · maxAttempts) pk] +
          ENNReal.ofReal (tvDist _ _) := by
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (tvDist_nonneg _ _),
              ENNReal.ofReal_toReal probOutput_ne_top]
      _ ≤ Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (progSignBody ids M pk sk · maxAttempts) pk] + slack :=
          add_le_add le_rfl h_games_tv
  -- Close: `slack ≤ ofReal(target)` via the `ℝ≥0∞` arithmetic.
  refine le_trans h_prob (add_le_add le_rfl ?_)
  rw [hslack]
  -- The starting cache is empty, so the resource base `R ∅` vanishes.
  have hR0 : R ((∅, []) : σ) = 0 := by rw [hR]; exact QueryCache.enncard_empty
  rw [hR0]
  rcases lt_or_ge ε 0 with hε | hε
  · -- `ε < 0`: the `ofReal ε` factors collapse `ζ` and `β` to `0`.
    have h0 : ENNReal.ofReal ε = 0 := ENNReal.ofReal_eq_zero.mpr hε.le
    have hζ0 : ζ = 0 := by rw [hζ, h0, zero_mul]
    have hβ0 : β = 0 := by rw [hβ, h0, zero_mul]
    rw [hζ0, hβ0, mul_zero, mul_zero, zero_add]
    exact bot_le
  · -- Main case: convert the `ℝ≥0∞` slack into `ofReal` of a real expression.
    set S : ℝ := ∑ a ∈ Finset.range maxAttempts, p_abort ^ a with hSdef
    set Tm : ℝ := ∑ a ∈ Finset.range maxAttempts, (a : ℝ) * p_abort ^ a with hTdef
    have hSnn : 0 ≤ S := Finset.sum_nonneg fun a _ => pow_nonneg hp₀ a
    have hTnn : 0 ≤ Tm :=
      Finset.sum_nonneg fun a _ => mul_nonneg (Nat.cast_nonneg a) (pow_nonneg hp₀ a)
    have hg_eq : g = ENNReal.ofReal S := by
      rw [hg, hSdef, ENNReal.ofReal_sum_of_nonneg (fun a _ => pow_nonneg hp₀ a)]
      exact Finset.sum_congr rfl fun a _ => by rw [← ENNReal.ofReal_pow hp₀]
    have hTsum : (∑ a ∈ Finset.range maxAttempts, (a : ℝ≥0∞) * ENNReal.ofReal p_abort ^ a)
        = ENNReal.ofReal Tm := by
      rw [hTdef, ENNReal.ofReal_sum_of_nonneg
        (fun a _ => mul_nonneg (Nat.cast_nonneg a) (pow_nonneg hp₀ a))]
      exact Finset.sum_congr rfl fun a _ => by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg a), ← ENNReal.ofReal_pow hp₀,
          ENNReal.ofReal_natCast]
    have hζ_eq : ζ = ENNReal.ofReal (ε * Tm) := by
      rw [hζ, hTsum, ← ENNReal.ofReal_mul hε]
    have hβ_eq : β = ENNReal.ofReal (ε * S) := by
      rw [hβ, hg_eq, ← ENNReal.ofReal_mul hε]
    -- The convolution bound `∑ a·pᵃ ≤ (∑ pᵃ)²` and the geometric bound `∑ pᵃ ≤ 1/(1-p)`.
    have hTS : Tm ≤ S ^ 2 := by
      rw [hTdef, hSdef]; exact sum_natCast_mul_pow_le_sq_sum_pow p_abort hp₀ maxAttempts
    have hSgeo : S ≤ 1 / (1 - p_abort) := by
      rw [hSdef, le_div_iff₀ h1p]
      have hmul := geom_sum_mul p_abort maxAttempts
      nlinarith [pow_nonneg hp₀ maxAttempts]
    rw [hζ_eq, hβ_eq, hg_eq, mul_zero, zero_add,
      show (qS : ℝ≥0∞) = ENNReal.ofReal qS from (ENNReal.ofReal_natCast qS).symm,
      show (qH : ℝ≥0∞) = ENNReal.ofReal qH from (ENNReal.ofReal_natCast qH).symm,
      show (qS.choose 2 : ℝ≥0∞) = ENNReal.ofReal (qS.choose 2) from
        (ENNReal.ofReal_natCast _).symm]
    rw [← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    -- Pure real inequality.
    have hchoose : (qS.choose 2 : ℝ) = qS * (qS - 1) / 2 := Nat.cast_choose_two ℝ qS
    have hqS : (0 : ℝ) ≤ qS := Nat.cast_nonneg qS
    have hqH : (0 : ℝ) ≤ qH := Nat.cast_nonneg qH
    have hS2 : S ^ 2 ≤ 1 / (1 - p_abort) ^ 2 := by
      have hsq : S ^ 2 ≤ (1 / (1 - p_abort)) ^ 2 := by gcongr
      rwa [div_pow, one_pow] at hsq
    have hTle : Tm ≤ 1 / (1 - p_abort) ^ 2 := le_trans hTS hS2
    have ht1 : ↑qS * (ε * Tm) ≤ qS * ε / (1 - p_abort) ^ 2 := by
      rw [show (qS : ℝ) * (ε * Tm) = (qS * ε) * Tm by ring,
        show (qS : ℝ) * ε / (1 - p_abort) ^ 2 = (qS * ε) * (1 / (1 - p_abort) ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left hTle (by positivity)
    have ht2 : ↑qS * ↑qH * (ε * S) ≤ qS * qH * ε / (1 - p_abort) := by
      rw [show (qS : ℝ) * qH * (ε * S) = (qS * qH * ε) * S by ring,
        show (qS : ℝ) * qH * ε / (1 - p_abort) = (qS * qH * ε) * (1 / (1 - p_abort)) by ring]
      exact mul_le_mul_of_nonneg_left hSgeo (by positivity)
    have ht3 : (qS.choose 2 : ℝ) * (ε * S ^ 2) ≤ (qS.choose 2 : ℝ) * ε / (1 - p_abort) ^ 2 := by
      rw [show (qS.choose 2 : ℝ) * (ε * S ^ 2) = ((qS.choose 2 : ℝ) * ε) * S ^ 2 by ring,
        show (qS.choose 2 : ℝ) * ε / (1 - p_abort) ^ 2
          = ((qS.choose 2 : ℝ) * ε) * (1 / (1 - p_abort) ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left hS2 (by positivity)
    have hcomb : ↑qS * (ε * Tm) + (↑qS * ↑qH + ↑(qS.choose 2) * S) * (ε * S)
        ≤ qS * ε / (1 - p_abort) ^ 2 + qS * qH * ε / (1 - p_abort)
          + (qS.choose 2 : ℝ) * ε / (1 - p_abort) ^ 2 := by
      rw [show (↑qS * ↑qH + ↑(qS.choose 2) * S) * (ε * S)
          = ↑qS * ↑qH * (ε * S) + (qS.choose 2 : ℝ) * (ε * S ^ 2) by ring]
      linarith [ht1, ht2, ht3]
    refine le_trans hcomb ?_
    rw [hchoose]
    have hne : (1 - p_abort) ^ 2 ≠ 0 := by positivity
    have hkey : (qS : ℝ) * ε / (1 - p_abort) ^ 2 + (qS * (qS - 1) / 2) * ε / (1 - p_abort) ^ 2
        = ↑qS * ε * (↑qS + 1) / (2 * (1 - p_abort) ^ 2) := by
      field_simp
      ring
    rw [show (qS : ℝ) * ε / (1 - p_abort) ^ 2 + qS * qH * ε / (1 - p_abort)
        + (qS * (qS - 1) / 2) * ε / (1 - p_abort) ^ 2
        = ((qS : ℝ) * ε / (1 - p_abort) ^ 2 + (qS * (qS - 1) / 2) * ε / (1 - p_abort) ^ 2)
          + qS * qH * ε / (1 - p_abort) by ring, hkey]
    have hextra : (qS : ℝ) * qH * ε / (1 - p_abort) ≤ qS * (qH + 1) * ε / (1 - p_abort) := by
      gcongr (?_ / (1 - p_abort))
      nlinarith [mul_nonneg hqS hε, hqS, hqH, hε]
    linarith [hextra]

omit [SampleableType Stmt] in
/-- Hop G₁ → G₂ (Prog → Trans) at a fixed key: dropping the reprogramming of rejected
attempts (keeping only the accepted transcript's programming) costs at most
`qS·(qH+1)·ε/(1-p)`.

Proof structure: both games are presented as projections of a single ghost-instrumented
run (`ghostHybridImpl`) over the two-layer cache, with rejected-attempt programmings
routed to the ghost layer. Overlaying the ghost layer recovers the Prog game
(`ghostHybridImpl_proj_prog`) and forgetting it recovers the Trans game
(`ghostHybridImpl_proj_trans`) — the deferred-sampling step. The two instrumented
handlers agree until the adversary reads a ghost point
(`tvDist_simulateQ_run_le_probEvent_output_bad`), the verification tail agrees by the
freshness check and the ghost-domain invariant
(`ghostHybridImpl_preserves_signed_inv`), and the firing probability is bounded by the
ghost-read collision charge `probEvent_ghostRead_bad_le`. -/
lemma probOutput_hybridExpAtKey_prog_le_trans
    (qS qH : ℕ) (ε p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1) (hε : 0 ≤ ε)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit)
    (hGuess : ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort) :
    Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (progSignBody ids M pk sk · maxAttempts) pk] ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (transSignBody ids M maxAttempts pk sk) pk] +
        ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
  classical
  set s₀ : ((M × Commit →ₒ Chal).QueryCache × (M × Commit →ₒ Chal).QueryCache) ×
      List M := ((∅, ∅), []) with hs₀
  set runP := (simulateQ (ghostHybridImpl ids M maxAttempts true pk sk)
    (adv.main pk)).run (s₀, false) with hrunP
  set runT := (simulateQ (ghostHybridImpl ids M maxAttempts false pk sk)
    (adv.main pk)).run (s₀, false) with hrunT
  set gP : (M × Option (Commit × Resp)) × GhostState M Commit Chal → ProbComp Bool :=
    fun z => hybridVerifyCont ids hr M maxAttempts pk
      (z.1, (overlayCache M z.2.1.1.1 z.2.1.1.2, z.2.1.2)) with hgP
  set gT : (M × Option (Commit × Resp)) × GhostState M Commit Chal → ProbComp Bool :=
    fun z => hybridVerifyCont ids hr M maxAttempts pk
      (z.1, (z.2.1.1.1, z.2.1.2)) with hgT
  -- Overlay projection of the instrumented run gives the Prog game.
  have hGP : hybridExpAtKey ids hr M maxAttempts adv
      (progSignBody ids M pk sk · maxAttempts) pk = runP >>= gP := by
    rw [hybridExpAtKey_eq_run_bind]
    have hproj := OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (ghostHybridImpl ids M maxAttempts true pk sk)
      (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
        hybridSignImpl M (progSignBody ids M pk sk · maxAttempts))
      (fun g : GhostState M Commit Chal => (overlayCache M g.1.1.1 g.1.1.2, g.1.2))
      (ghostHybridImpl_proj_prog ids M maxAttempts pk sk)
      (adv.main pk) (s₀, false)
    have hinit : (overlayCache M ((s₀, false) : GhostState M Commit Chal).1.1.1
          (s₀, false).1.1.2, ((s₀, false) : GhostState M Commit Chal).1.2) =
        ((∅, []) : (M × Commit →ₒ Chal).QueryCache × List M) := by
      simp [hs₀, overlayCache_empty]
    rw [hinit] at hproj
    rw [← hproj, bind_map_left]
    exact bind_congr fun z => rfl
  -- Ghost-forgetting projection of the instrumented run gives the Trans game.
  have hGT : hybridExpAtKey ids hr M maxAttempts adv
      (transSignBody ids M maxAttempts pk sk) pk = runT >>= gT := by
    rw [hybridExpAtKey_eq_run_bind]
    have hproj := OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (ghostHybridImpl ids M maxAttempts false pk sk)
      (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
        hybridSignImpl M (transSignBody ids M maxAttempts pk sk))
      (fun g : GhostState M Commit Chal => (g.1.1.1, g.1.2))
      (ghostHybridImpl_proj_trans ids M maxAttempts pk sk)
      (adv.main pk) (s₀, false)
    have hinit : ((((s₀, false) : GhostState M Commit Chal).1.1.1,
          ((s₀, false) : GhostState M Commit Chal).1.2)) =
        ((∅, []) : (M × Commit →ₒ Chal).QueryCache × List M) := by
      simp [hs₀]
    rw [hinit] at hproj
    rw [← hproj, bind_map_left]
    exact bind_congr fun z => rfl
  -- Identical-until-bad on the instrumented runs.
  have h_bad :=
    OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
      (ghostHybridImpl ids M maxAttempts true pk sk)
      (ghostHybridImpl ids M maxAttempts false pk sk)
      (adv.main pk) s₀
      (ghostHybridImpl_agree_good ids M maxAttempts pk sk)
      (ghostHybridImpl_bad_mono ids M maxAttempts true pk sk)
      (ghostHybridImpl_bad_mono ids M maxAttempts false pk sk)
  set Pbad := Pr[fun z : (M × Option (Commit × Resp)) × GhostState M Commit Chal =>
    z.2.2 = true | runP] with hPbad
  -- Ghost-domain invariant along the Trans-side run.
  have h_inv : ∀ z ∈ support runT,
      ∀ q : M × Commit, z.2.1.1.2 q ≠ none → q.1 ∈ z.2.1.2 := by
    intro z hz
    exact OracleComp.simulateQ_run_preserves_inv_of_query
      (ghostHybridImpl ids M maxAttempts false pk sk)
      (fun g : GhostState M Commit Chal =>
        ∀ q : M × Commit, g.1.1.2 q ≠ none → q.1 ∈ g.1.2)
      (fun t s hs =>
        ghostHybridImpl_preserves_signed_inv ids M maxAttempts false pk sk t s hs)
      (adv.main pk) (s₀, false) (fun q hq => by simp [hs₀] at hq)
      z hz
  -- The two verification continuations agree on the Trans-side support.
  have h_eqT : Pr[= true | runT >>= gP] = Pr[= true | runT >>= gT] := by
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ support runT
    · congr 1
      by_cases hmem : z.1.1 ∈ z.2.1.2
      · rw [hgP, hgT]
        rw [probOutput_true_hybridVerifyCont_of_mem ids hr M maxAttempts pk
            z.1 _ z.2.1.2 hmem,
          probOutput_true_hybridVerifyCont_of_mem ids hr M maxAttempts pk
            z.1 _ z.2.1.2 hmem]
      · have hagree : ∀ w : Commit,
            overlayCache M z.2.1.1.1 z.2.1.1.2 (z.1.1, w) = z.2.1.1.1 (z.1.1, w) := by
          intro w
          refine overlayCache_apply_ghost_none (M := M) _ ?_
          by_contra hne
          exact hmem (h_inv z hz (z.1.1, w) hne)
        rw [hgP, hgT]
        exact congrArg (fun x => Pr[= true | x])
          (hybridVerifyCont_cache_congr ids hr M maxAttempts pk z.1 _ _ z.2.1.2 hagree)
    · simp [probOutput_eq_zero_of_not_mem_support hz]
  -- Combine: TV budget plus the (open) collision charge.
  have h_tv : tvDist (runP >>= gP) (runT >>= gP) ≤ Pbad.toReal :=
    le_trans (tvDist_bind_right_le gP runP runT) h_bad
  have h_badBound : Pbad ≤ ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) :=
    probEvent_ghostRead_bad_le ids hr M maxAttempts adv qS qH ε p_abort hp₀ hp hε hQ pk sk
      hGuess hAbort
  have h_real : Pr[= true | runP >>= gP].toReal ≤
      Pr[= true | runT >>= gT].toReal + Pbad.toReal := by
    have habs := abs_probOutput_toReal_sub_le_tvDist (runP >>= gP) (runT >>= gP)
    have h2 := (abs_le.mp habs).2
    rw [h_eqT] at h2
    linarith [h_tv]
  have hPbad_ne_top : Pbad ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one
  calc Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (progSignBody ids M pk sk · maxAttempts) pk]
      = Pr[= true | runP >>= gP] := by rw [hGP]
    _ = ENNReal.ofReal (Pr[= true | runP >>= gP].toReal) :=
        (ENNReal.ofReal_toReal probOutput_ne_top).symm
    _ ≤ ENNReal.ofReal (Pr[= true | runT >>= gT].toReal + Pbad.toReal) :=
        ENNReal.ofReal_le_ofReal h_real
    _ = Pr[= true | runT >>= gT] + Pbad := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal probOutput_ne_top, ENNReal.ofReal_toReal hPbad_ne_top]
    _ ≤ Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (transSignBody ids M maxAttempts pk sk) pk] +
        ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) := by
        rw [hGT]
        exact add_le_add le_rfl h_badBound

omit [SampleableType Stmt] in
/-- Hop G₂ → G₃ (Trans → Sim) at a fixed key: replacing the private honest-execution
loop by the per-attempt HVZK simulator loop costs at most `qS·ζ_zk/(1-p)`.

Distributional content: per signing query, `transSignBody` and `simSignBody` differ only
in the optional sampler driving `firstSome`; `tvDist_firstSome_le_geometric` bounds the
per-query gap by `ζ_zk · (1 + p + ⋯) ≤ ζ_zk/(1-p)` using `ids.HVZK sim ζ_zk` (`hhvzk`)
and the simulator abort bound (`hAbortSim`), uniformly in the shared starting cache
(`tvDist_run_transSignBody_simSignBody_le`). The per-query total-variation budget is
accumulated across the at-most-`qS` signing queries of the adversary run by
`tvDist_simulateQ_run_le_queryBoundP_mul`, the two hybrid handlers agreeing exactly on
the base (uniform and random-oracle) component. -/
lemma probOutput_hybridExpAtKey_trans_le_sim
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk) (hhvzk : ids.HVZK sim ζ_zk)
    (qS qH : ℕ) (p_abort : ℝ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH)
    (pk : Stmt) (sk : Wit) (hrel : rel pk sk = true)
    (hAbortSim : Pr[= none | sim pk] ≤ ENNReal.ofReal p_abort) :
    Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (transSignBody ids M maxAttempts pk sk) pk] ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (simSignBody M maxAttempts sim pk sk) pk] +
        ENNReal.ofReal (qS * ζ_zk / (1 - p_abort)) := by
  set ε : ℝ := ζ_zk * ∑ j ∈ Finset.range maxAttempts, p_abort ^ j with hε_def
  have hε_nonneg : 0 ≤ ε :=
    mul_nonneg hζ (Finset.sum_nonneg fun j _ => pow_nonneg hp₀ j)
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  -- The simulator abort bound, in real form.
  have hq_toReal : Pr[= none | sim pk].toReal ≤ p_abort := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hAbortSim
    rwa [ENNReal.toReal_ofReal hp₀] at h
  -- Per-signing-query step bound, uniform over the hybrid state.
  have h_step : ∀ (msg : M) (s : (M × Commit →ₒ Chal).QueryCache × List M),
      tvDist ((hybridSignImpl M (transSignBody ids M maxAttempts pk sk) msg).run s)
        ((hybridSignImpl M (simSignBody M maxAttempts sim pk sk) msg).run s) ≤ ε := by
    intro msg s
    have hrun : ∀ (body : M → StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp
        (Option (Commit × Resp))),
        (hybridSignImpl M body msg).run s =
          (fun (ac : Option (Commit × Resp) × (M × Commit →ₒ Chal).QueryCache) =>
            (ac.1, (ac.2, msg :: s.2))) <$> (body msg).run s.1 := by
      intro body
      rfl
    rw [hrun, hrun]
    exact le_trans (tvDist_map_le _ _ _)
      (tvDist_run_transSignBody_simSignBody_le ids M maxAttempts sim pk sk hrel msg
        hhvzk hq_toReal hp₀ s.1)
  -- Accumulate the per-query budget across the `qS` signing queries of the run.
  have h_run : tvDist
      (StateT.run (simulateQ
        (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (transSignBody ids M maxAttempts pk sk)) (adv.main pk)) (∅, []))
      (StateT.run (simulateQ
        (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
          hybridSignImpl M (simSignBody M maxAttempts sim pk sk)) (adv.main pk)) (∅, []))
        ≤ qS * ε := by
    refine OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_queryBoundP_mul
      _ _ hε_nonneg
      (· matches .inr _) ?_ ?_ (adv.main pk) (hQ pk).1 (∅, [])
    · rintro (t | msg) hSt s
      · simp at hSt
      · simpa only [QueryImpl.add_apply_inr] using h_step msg s
    · rintro (t | msg) hSt s
      · simp only [QueryImpl.add_apply_inl]
      · simp at hSt
  -- The verification continuation is shared, so the games inherit the run-level bound.
  have h_tv_games : tvDist
      (hybridExpAtKey ids hr M maxAttempts adv (transSignBody ids M maxAttempts pk sk) pk)
      (hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim pk sk) pk)
        ≤ qS * ε := by
    refine le_trans ?_ h_run
    simp only [hybridExpAtKey]
    exact tvDist_bind_right_le _ _ _
  -- Close the finite geometric sum: `∑_{j<n} p^j ≤ 1/(1-p)`.
  have hsum_le : ∑ j ∈ Finset.range maxAttempts, p_abort ^ j ≤ 1 / (1 - p_abort) := by
    rw [le_div_iff₀ h1p]
    have hmul := geom_sum_mul p_abort maxAttempts
    nlinarith [pow_nonneg hp₀ maxAttempts]
  have h_bound : (qS : ℝ) * ε ≤ qS * ζ_zk / (1 - p_abort) := by
    rw [hε_def, div_eq_mul_inv, ← one_div]
    calc (qS : ℝ) * (ζ_zk * ∑ j ∈ Finset.range maxAttempts, p_abort ^ j)
        ≤ (qS : ℝ) * (ζ_zk * (1 / (1 - p_abort))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left hsum_le hζ
      _ = (qS : ℝ) * ζ_zk * (1 / (1 - p_abort)) := by ring
  have h_loss_nonneg : (0 : ℝ) ≤ qS * ζ_zk / (1 - p_abort) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hζ) h1p.le
  -- Convert the real TV bound into the `ℝ≥0∞` output-probability bound.
  have h_real : Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (transSignBody ids M maxAttempts pk sk) pk].toReal ≤
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (simSignBody M maxAttempts sim pk sk) pk].toReal +
        qS * ζ_zk / (1 - p_abort) := by
    have habs := abs_probOutput_toReal_sub_le_tvDist
      (hybridExpAtKey ids hr M maxAttempts adv (transSignBody ids M maxAttempts pk sk) pk)
      (hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim pk sk) pk)
    have h_le := (abs_le.mp habs).2
    linarith [h_tv_games, h_bound]
  calc Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (transSignBody ids M maxAttempts pk sk) pk]
      = ENNReal.ofReal (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (transSignBody ids M maxAttempts pk sk) pk].toReal) :=
        (ENNReal.ofReal_toReal probOutput_ne_top).symm
    _ ≤ ENNReal.ofReal (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (simSignBody M maxAttempts sim pk sk) pk].toReal +
          qS * ζ_zk / (1 - p_abort)) := ENNReal.ofReal_le_ofReal h_real
    _ = Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (simSignBody M maxAttempts sim pk sk) pk] +
          ENNReal.ofReal (qS * ζ_zk / (1 - p_abort)) := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg h_loss_nonneg,
          ENNReal.ofReal_toReal probOutput_ne_top]

/-! ## The NMA reduction

### Named managed/runtime handlers for the linked-run coupling

The managed NMA run is a two-layer nested simulation: an *inner managed* handler
`nmaOuterImpl pk` (forward uniform, managed-cache RO reads, simulator-loop signing) threads
the inner cache, and an *outer runtime* handler `nmaInnerImpl` (`unifFwdImpl + randomOracle`)
re-simulates the residual live queries. Their `link`, `nmaLinkImpl pk`, is the single
combined simulation over the product cache that the per-step state-coupling projects onto.
These were previously inline `letI` bindings inside `simulatedNmaAdv` and
`managedRun_eq_link_run`; promoting them to top level makes `nmaLinkImpl pk` a nameable
handler so the coupling can be stated and proved one query step at a time. -/

omit [SampleableType Stmt] [DecidableEq Commit] [SampleableType Chal] [DecidableEq M] in
/-- **Uniform-only nested-simulation collapse (sub-lemma (b), part (i) — PROVEN, axiom-clean).**
The simulator loop inside `sigSim`/`nmaOuterImpl` is run under the inner managed handler's
uniform branch `unifSim n = fwd (.inl n)`, which forwards each uniform draw transparently into
the sum spec without touching the managed cache. Hence simulating any `unifSpec`-only
computation `oa` under `unifSim` and running the resulting `StateT` at a cache `cache` returns
`oa` lifted into the sum spec with the cache threaded *unchanged*: `(simulateQ unifSim oa).run
cache = (·, cache) <$> liftComp oa _`. This collapses the `simulateQ unifSim (firstSome (sim
pk) maxAttempts)` nested simulation in the sign step back to the bare lifted `firstSome` loop —
the part of `hproj2_sign` that is independent of the live-read/sign collision. -/
lemma simulateQ_unifSim_run {α : Type}
    (oa : OracleComp unifSpec α)
    (cache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache) :
    let spec := unifSpec + (M × Commit →ₒ Chal)
    let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
    let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
      fun n => fwd (.inl n)
    (simulateQ unifSim oa).run cache =
      (fun r => (r, cache)) <$> (liftComp oa (unifSpec + (M × Commit →ₒ Chal))) := by
  intro spec fwd unifSim
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x => simp [unifSim, fwd]
  | query_bind t k ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_query]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
      -- `unifSim t` forwards the uniform query `t` straight through into the sum spec, leaving
      -- the cache untouched.
      have hstep : (unifSim t).run cache
          = (liftComp (query t : OracleComp unifSpec _) spec) >>= fun u => pure (u, cache) := by
        simp only [unifSim, fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
        change ((liftM (query (Sum.inl t)) :
            StateT (unifSpec + (M × Commit →ₒ Chal)).QueryCache
              (OracleComp (unifSpec + (M × Commit →ₒ Chal))) _)).run cache = _
        rw [OracleComp.liftM_run_StateT]
        refine congrArg (· >>= fun u => pure (u, cache)) ?_
        rfl
      rw [hstep, liftComp_bind, map_bind, bind_assoc]
      simp only [pure_bind]
      exact bind_congr (fun u => ih u cache)

/-- The inner *managed* handler of the NMA reduction: forward uniform queries to the live
spec (`unifSim`), answer hash queries through the managed cache (`roSim`, forwarding misses
to the live oracle), and answer signing queries with the simulator loop (`sigSim`), programming
the accepted transcript's challenge into the managed cache. This is the
`(unifSim + roSim) + sigSim` handler used inside `simulatedNmaAdv`. -/
noncomputable def nmaOuterImpl (pk : Stmt) :
    QueryImpl.Stateful (unifSpec + (M × Commit →ₒ Chal))
      ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      (unifSpec + (M × Commit →ₒ Chal)).QueryCache :=
  letI spec := unifSpec + (M × Commit →ₒ Chal)
  letI fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  letI unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  letI roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none => do
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  letI sigSim : QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun msg => do
    let r ← simulateQ unifSim (firstSome (sim pk) maxAttempts)
    match r with
    | some (w, c, z) =>
        modifyGet fun cache => (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
    | none => pure none
  (unifSim + roSim) + sigSim

/-- The outer *runtime* handler of the NMA reduction: forward uniform queries (`unifFwdImpl`)
and answer the residual live random-oracle reads through the runtime's own random oracle
(`randomOracle`), threading the outer cache. This is the
`unifFwdImpl + randomOracle` handler that re-simulates the `.run ∅` boundary in
`simulatedNmaAdv`. -/
noncomputable def nmaInnerImpl :
    QueryImpl.Stateful unifSpec (unifSpec + (M × Commit →ₒ Chal))
      ((M × Commit →ₒ Chal).QueryCache) :=
  unifFwdImpl (M × Commit →ₒ Chal) +
    (randomOracle : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))

/-- The single *linked* handler `nmaOuterImpl pk |>.link nmaInnerImpl` that collapses the
two-layer managed/runtime nesting into one simulation over the product cache
`((unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache)`.
The per-step state-coupling for the NMA bridge is stated against this handler. -/
noncomputable def nmaLinkImpl (pk : Stmt) :
    QueryImpl.Stateful unifSpec
      ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp)))
      ((unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache) :=
  (nmaOuterImpl M maxAttempts sim pk).link (nmaInnerImpl M)

/-- The linked-run projection of sub-lemma (b): map the layered ghost-tagged NMA state
`((base, ghost), signed)` onto the linked managed handler's product cache pair.

The product cache the linked handler `nmaLinkImpl` carries is
`(inner : (unifSpec + (M × Commit →ₒ Chal)).QueryCache, outer : (M × Commit →ₒ Chal).QueryCache)`,
where the **inner** managed cache accumulates *both* live random-oracle reads (`roSim` writes a
fresh value into the inner `.inr mc` slot) *and* the signing-programmed accepted transcripts
(`sigSim` writes `.inr (msg, w) ↦ c`), while the **outer** runtime cache accumulates *only* live
random-oracle reads (`sigSim` never forwards to the outer oracle).

Hence the consistent per-step projection is:

* `inner := baseEmbed (overlayCache base ghost)` — the *full* hybrid cache (live reads in the
  base layer plus signing-programmed points in the ghost layer), embedded into the sum-keyed
  inner cache; and
* `outer := base` — the live-read base layer only.

This is the corrected projection: an earlier attempt set `inner := baseEmbed base` and
`outer := overlayCache base ghost`, which is inconsistent — the random-oracle step writes a
live read into the inner cache (so it must carry the overlay), while the signing step writes
the programmed transcript into the inner cache and never touches the outer (so the outer must
exclude ghost points). With `inner := baseEmbed (overlay base ghost)` and `outer := base` both
the RO step and the sign step become exact per-step equalities. The signed-message list is
forgotten — the linked handler carries no such list. -/
def proj2 (s : NmaGhostState M Commit Chal) :
    (unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache :=
  (baseEmbed M (overlayCache M s.1.1 s.1.2), s.1.1)

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), uniform-query step.** On a uniform query the layered ghost-tagged
handler `ghostNmaImpl`, projected by `proj2`, matches the linked managed handler `nmaLinkImpl`
applied to the projected state. The uniform query forwards straight through both handlers
(`unifSim`/`unifFwdImpl`) without touching either cache layer, so the coupling is the
straightforward forward pass. -/
lemma hproj2_unif (pk : Stmt) (sk : Wit) (n : unifSpec.Domain)
    (s : NmaGhostState M Commit Chal) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inl n))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inl n))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_unif, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
    HasQuery.toQueryImpl_apply, nmaInnerImpl, unifFwdImpl, proj2]
  rfl

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), random-oracle step — cached-read sub-case.** On a random-oracle query at a
point `mc` whose ghost layer misses (`hgm`) and whose base layer already holds a value `v`
(`hbh : s.1.1 mc = some v`), the layered ghost-tagged handler `ghostNmaImpl`, projected by
`proj2`, matches the linked managed handler `nmaLinkImpl` applied to the projected state. Both
sides read the cached value: `ghostNmaImpl` returns `roStep`'s cached branch (base hit), while
the linked `roSim` finds the same value in the inner managed cache (`baseEmbed base`, which holds
the base entry at `.inr mc`) and short-circuits, so neither cache layer is written.

The two RO sub-cases left open (gated by the reachable-state invariant, see `hproj2_sign`'s
docstring and the residual in `hybridSimRun_le_managedRun_verify`) are:

* **fresh live read** (`s.1.1 mc = none`, ghost miss): the read resamples; both sides write the
  sampled value to base/inner (`baseEmbed_cacheQuery`) and to overlay/outer
  (`overlayCache_cacheQuery_real_of_ghost_none`, via the `randomOracle_run_eq_roStep` round-trip).
  This is true and reduces to a `roStep`-on-`overlayCache` match, but the inner-`roSim` /
  outer-`randomOracle` nested-simulation `.run` plumbing is part of the deferred coupling.
* **ghost hit** (`s.1.2 mc ≠ none`): genuinely *not* a per-step state projection — `ghostNmaImpl`
  returns the ghost value leaving its state untouched, whereas the linked `roSim` re-reads through
  the runtime `randomOracle` (recovering the same value from `overlayCache base ghost`) but
  *writes it back* into the inner managed cache's `.inr mc` slot, so the two final inner caches
  differ by exactly that re-cached point. Reconciling it needs the reachable-state invariant "a
  ghost point is never separately live-read" rather than a pointwise projection. -/
lemma hproj2_ro (pk : Stmt) (sk : Wit) (mc : M × Commit) (v : Chal)
    (s : NmaGhostState M Commit Chal) (hgm : s.1.2 mc = none) (hbh : s.1.1 mc = some v) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inr mc))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_ro, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, proj2]
  rw [hgm]
  -- The inner managed cache is now `baseEmbed (overlayCache base ghost)`; since the ghost layer
  -- misses at `mc` (`hgm`), the overlay agrees with the base layer there (`= some v`), so `roSim`
  -- finds the value in the inner cache and short-circuits without touching either cache layer.
  have hov : overlayCache M s.1.1 s.1.2 mc = some v :=
    (overlayCache_apply_ghost_none (M := M) s.1.1 hgm).trans hbh
  erw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind, baseEmbed_inr, hov, roStep_of_some M hbh, map_pure, nmaInnerImpl]
  erw [StateT.run_pure]
  simp only [map_pure, QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst, PFunctor.Lens.State.snd, Prod.map, id_eq, proj2]
  rfl

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), random-oracle step — ghost-hit sub-case.** On a random-oracle query at a
point `mc` whose ghost layer already holds a value `v` (`hgh : s.1.2 mc = some v`), the layered
ghost-tagged handler `ghostNmaImpl`, projected by `proj2`, matches the linked managed handler
`nmaLinkImpl` applied to the projected state. `ghostNmaImpl` returns the ghost value leaving its
state untouched; under the *redesigned* `proj2` the inner managed cache is `baseEmbed (overlay
base ghost)`, which carries the ghost value at `.inr mc` (`overlayCache_apply_ghost_some`), so the
linked `roSim` finds it and short-circuits without touching either layer. (Under the earlier
`proj2 = (baseEmbed base, …)` this case diverged — the inner cache did not hold ghost points — and
needed a reachability invariant; the redesign makes it exact.) -/
lemma hproj2_ro_ghost_hit (pk : Stmt) (sk : Wit) (mc : M × Commit) (v : Chal)
    (s : NmaGhostState M Commit Chal) (hgh : s.1.2 mc = some v) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inr mc))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_ro, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, proj2]
  rw [hgh]
  -- The overlay holds the ghost value at `mc`, so the inner managed cache `baseEmbed (overlay
  -- base ghost)` does too; `roSim` short-circuits.
  have hov : overlayCache M s.1.1 s.1.2 mc = some v :=
    overlayCache_apply_ghost_some (M := M) s.1.1 hgh
  erw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind, baseEmbed_inr, hov, map_pure, nmaInnerImpl]
  erw [StateT.run_pure]
  simp only [map_pure, QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst, PFunctor.Lens.State.snd, Prod.map, id_eq, proj2]
  rfl

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), random-oracle step — fresh-live-read sub-case.** On a random-oracle
query at a point `mc` whose ghost layer misses (`hgm`) and whose base layer also misses
(`hbm : s.1.1 mc = none`), the layered ghost-tagged handler `ghostNmaImpl`, projected by
`proj2`, matches the linked managed handler `nmaLinkImpl` applied to the projected state.
Both sides resample a fresh value `c`; `ghostNmaImpl` writes it to the base layer (`roStep`'s
miss branch), while the linked `roSim` misses the inner managed cache (`baseEmbed base`,
which has no entry at `.inr mc` since `base mc = none`) and forwards to the runtime
`randomOracle` (the `randomOracle_run_eq_roStep` round-trip), caching the result both in the
inner managed cache and the outer runtime cache. Under `proj2`, the inner write matches
`baseEmbed_cacheQuery` and the outer write matches `overlayCache_cacheQuery_real_of_ghost_none`. -/
lemma hproj2_ro_fresh (pk : Stmt) (sk : Wit) (mc : M × Commit)
    (s : NmaGhostState M Commit Chal) (hgm : s.1.2 mc = none) (hbm : s.1.1 mc = none) :
    Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inl (.inr mc))).run s =
      (nmaLinkImpl M maxAttempts sim pk (.inl (.inr mc))).run (proj2 M s) := by
  rw [ghostNmaImpl_run_ro, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [nmaOuterImpl, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, proj2]
  rw [hgm]
  -- The inner managed cache is now `baseEmbed (overlayCache base ghost)`; since both the ghost
  -- layer (`hgm`) and the base layer (`hbm`) miss at `mc`, the overlay misses there too, so
  -- `roSim`'s inner lookup misses and forwards to the outer runtime `randomOracle`.
  have hov : overlayCache M s.1.1 s.1.2 mc = none := by simp [overlayCache, hgm, hbm]
  erw [StateT.run_bind, StateT.run_get]
  simp only [pure_bind, baseEmbed_inr, hov]
  rw [QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
  -- Reduce the inner `roSim` body run to a single `query` followed by an inner-cache write,
  -- then push `simulateQ nmaInnerImpl` through it: the `.inr mc` query is answered by the
  -- runtime `randomOracle`, whose run is `roStep` on the outer cache.
  conv_rhs =>
    enter [2, 1, 2]
    change (query (Sum.inr mc) : OracleComp (unifSpec + (M × Commit →ₒ Chal)) _) >>=
      fun v => pure (v, (baseEmbed M (overlayCache M s.1.1 s.1.2)).cacheQuery (Sum.inr mc) v)
  rw [simulateQ_bind]
  simp only [simulateQ_pure]
  conv_rhs =>
    enter [2, 1, 1]
    rw [show (query (Sum.inr mc) : OracleComp (unifSpec + (M × Commit →ₒ Chal)) _) =
        liftM ((unifSpec + (M × Commit →ₒ Chal)).query (Sum.inr mc)) from rfl,
      simulateQ_spec_query]
    simp only [nmaInnerImpl, QueryImpl.add_apply_inr]
  rw [StateT.run_bind]
  conv_rhs => enter [2, 1]; erw [randomOracle_run_eq_roStep]
  -- Both sides resample: the layered run's base layer and the linked run's outer cache (now the
  -- base layer too) both miss at `mc`.
  rw [roStep_of_none M hbm]
  -- Normalise both sides to a single resample, mapping `c` to a `(c, inner, outer)` triple.
  simp only [bind_pure_comp, StateT.run_pure]
  conv_lhs => erw [Functor.map_map, Functor.map_map]
  conv_rhs => erw [Functor.map_map, Functor.map_map]
  refine map_congr fun c => ?_
  -- Reconcile the cache writes on the two layers: the inner write matches `baseEmbed`'s
  -- `cacheQuery`, the outer write matches the overlay's `cacheQuery` (ghost misses at `mc`).
  simp only [Prod.map, id_eq, proj2, QueryImpl.Stateful.Frame.linkReshape,
    QueryImpl.Stateful.Frame.prod, PFunctor.Lens.State.fst, PFunctor.Lens.State.snd,
    PFunctor.Lens.State.put, PFunctor.Lens.State.mk]
  rw [overlayCache_cacheQuery_real_of_ghost_none (M := M) s.1.1 hgm, baseEmbed_cacheQuery]

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), signing-query step — exact per-step equality.**

On a signing query, the layered ghost-tagged handler `ghostNmaImpl`, projected by the
*redesigned* `proj2 ((base, ghost), signed) = (baseEmbed (overlayCache base ghost), base)`,
equals the linked managed handler `nmaLinkImpl` applied to the projected state — *unconditionally*
(no collision hypothesis).

The redesign is what makes this exact. The linked managed `sigSim` writes the accepted transcript
into the *inner managed cache* (`cacheQuery (.inr (msg, w)) c`) and leaves the *outer runtime
cache* untouched. The layered run writes the same transcript into the *ghost layer*, leaving the
base layer untouched. Under the new `proj2`, the inner managed cache is recovered as `baseEmbed`
of the *full overlay* `overlayCache base ghost`, so the ghost-layer write surfaces in `proj2`'s
*first* slot exactly where `sigSim` writes (`overlayCache_cacheQuery_ghost` then
`baseEmbed_cacheQuery`), while the outer cache is `proj2`'s *second* slot `base`, untouched on both
sides. There is no slot swap and no dependence on whether `(msg, w)` coincides with a prior live
read: `proj2`'s first component carries the full overlay, so the sign point lands in the same inner
slot regardless. (This supersedes the earlier `proj2 = (baseEmbed base, overlayCache base ghost)`
projection, for which this step was provably *not* a per-step state function.)

PROOF SHAPE. `link_impl_apply_run` exposes the linked RHS as the nested simulation
`simulateQ nmaInnerImpl ((nmaOuterImpl pk (.inr msg)).run outerCache)`; `simp [nmaOuterImpl]`
reduces the outer step to the `sigSim` body — a nested `simulateQ unifSim (firstSome (sim pk)
maxAttempts)` (collapsed by `simulateQ_unifSim_run`, the simulator loop touches no cache layer)
followed by inner-cache programming `cacheQuery (.inr (msg, w)) c`. The LHS is `simGhostSignBody`
(`liftM (firstSome (sim pk) maxAttempts)` then ghost-layer `cacheQuery (msg, w) c`). A
support-restricted `SPMF` bind congruence on the accepted transcript then reduces both sides to
matching pure values, closed by the overlay/`baseEmbed` cache algebra above. -/
lemma hproj2_sign (pk : Stmt) (sk : Wit) (msg : M)
    (s : NmaGhostState M Commit Chal) :
    𝒟[Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk (.inr msg)).run s] =
      𝒟[(nmaLinkImpl M maxAttempts sim pk (.inr msg)).run (proj2 M s)] := by
  rw [ghostNmaImpl_run_sign, nmaLinkImpl, QueryImpl.Stateful.link_impl_apply_run]
  -- Reduce the linked RHS's outer step `nmaOuterImpl pk (.inr msg)` to the simulator body
  -- `sigSim msg`: a nested simulation `simulateQ unifSim (firstSome (sim pk) maxAttempts)`
  -- followed by inner-cache programming of the accepted transcript. After this the residual is
  -- the uniform-only nested-simulation collapse (i) above; the per-step equality then fails
  -- exactly on `signLiveCollision`, which the leaf's collision-accounting reframe pays on the
  -- bad side rather than discharging here.
  simp only [nmaOuterImpl, QueryImpl.add_apply_inr]
  -- Reduce the LHS to `firstSome (sim pk) maxAttempts >>= ghostSignProgramCont`.
  simp only [simGhostSignBody, StateT.run_bind, OracleComp.liftM_run_StateT, bind_assoc,
    pure_bind, map_bind]
  -- Collapse the RHS's nested `simulateQ unifSim (firstSome …)` loop via `simulateQ_unifSim_run`.
  conv_rhs => enter [1, 2, 1]; erw [StateT.run_bind]; rw [simulateQ_unifSim_run]
  -- Distribute the outer `simulateQ nmaInnerImpl` and `.run` over the bind, and collapse the
  -- lifted `firstSome` loop against `nmaInnerImpl`'s uniform-forwarding branch (`roSim`).
  rw [simulateQ_bind, StateT.run_bind, simulateQ_map, StateT.run_map]
  rw [show nmaInnerImpl M = unifFwdImpl (M × Commit →ₒ Chal) +
      (randomOracle : QueryImpl (M × Commit →ₒ Chal)
        (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)) from rfl,
    roSim.simulateQ_liftComp, unifFwdImpl.simulateQ_run]
  -- Both sides are now `firstSome … >>= (per-output programming)`; align by support-restricted
  -- bind congruence and case-split on the accepted transcript.
  simp only [map_bind, Functor.map_map, bind_map_left]
  -- Move into `SPMF` (where the map/bind laws apply cleanly, dodging the `OracleComp` `Functor`
  -- vs `Monad` map friction): both sides become `𝒟[firstSome …] >>= (per-output programming)`.
  simp only [evalDist_map, evalDist_bind]
  conv_lhs => enter [2]; erw [evalDist_bind]
  rw [map_bind]
  -- Support-restricted `SPMF` bind congruence (`evalDist_bind_congr` with `m := SPMF`, where
  -- `evalDist` is the identity): case-split on the accepted transcript, using the no-collision
  -- hypothesis on the `some` branch.
  refine evalDist_bind_congr (m := SPMF) (mx := 𝒟[firstSome (sim pk) maxAttempts])
    fun a _ha => ?_
  simp only [SPMF.evalDist_def]
  -- Case-split on the accepted transcript; under the redesigned `proj2` the `some` branch aligns
  -- the ghost-layer write with the inner-cache write unconditionally (no collision hypothesis).
  cases a with
  | none =>
      -- The all-abort outcome programs no point on either side; both reduce to `(none, proj2 s)`.
      simp only [ghostSignProgramCont, StateT.run_pure]
      conv_rhs => enter [2, 1, 1, 2]; erw [StateT.run_pure]
      conv_rhs => enter [2, 1, 1]; rw [simulateQ_pure]
      conv_rhs => enter [2, 1]; erw [StateT.run_pure]
      simp only [evalDist_pure, map_pure, proj2, QueryImpl.Stateful.Frame.linkReshape,
        QueryImpl.Stateful.Frame.prod, PFunctor.Lens.State.fst, PFunctor.Lens.State.snd,
        PFunctor.Lens.State.put, PFunctor.Lens.State.mk]
      conv_lhs => erw [evalDist_pure]; rw [map_pure]
      simp only [proj2, Prod.map, id_eq]
  | some wcz =>
      obtain ⟨w, c, z⟩ := wcz
      -- Reduce the LHS ghost-layer programming to a pure value.
      simp only [ghostSignProgramCont, StateT.run_bind, StateT.run_modify, pure_bind,
        StateT.run_pure, map_pure]
      -- Reduce the RHS inner-cache programming and the trivial outer simulation to a pure value.
      conv_rhs => enter [2, 1, 1, 2]; erw [StateT.run_modifyGet]
      rw [simulateQ_pure]
      erw [StateT.run_pure]
      simp only [evalDist_pure, map_pure, proj2, QueryImpl.Stateful.Frame.linkReshape,
        QueryImpl.Stateful.Frame.prod, PFunctor.Lens.State.fst, PFunctor.Lens.State.snd,
        PFunctor.Lens.State.put, PFunctor.Lens.State.mk]
      conv_lhs => erw [evalDist_pure]; rw [map_pure]
      simp only [proj2, Prod.map, id_eq]
      -- Off the collision (`hbase : s.1.1 (msg, w) = none`) the two pure values agree exactly under
      -- the *redesigned* `proj2 ((base, ghost), signed) = (baseEmbed (overlay base ghost), base)`.
      -- Both sides write the accepted transcript into the inner managed cache and leave the outer
      -- (live-read) cache `base` untouched:
      --   LHS = (some (w, z), baseEmbed (overlay base (ghost.cacheQuery (msg, w) c)), base)
      --   RHS = (some (w, z), (baseEmbed (overlay base ghost)).cacheQuery (.inr (msg, w)) c, base).
      -- The ghost-layer write surfaces in the inner cache (`proj2`'s *first* slot, via the overlay)
      -- exactly where the linked `sigSim` writes `.inr (msg, w) ↦ c`, and the live-read layer
      -- `base` (`proj2`'s *second* slot = the linked outer cache) is untouched on both sides — so
      -- the per-step sign equality is now exact (no slot swap). The `hbase` no-collision hypothesis
      -- is not even needed for the cache algebra under the redesigned projection: `proj2`'s first
      -- component carries the full overlay, so the sign point lands in the same inner slot whether
      -- or not it coincides with a prior live read.
      rw [overlayCache_cacheQuery_ghost, baseEmbed_cacheQuery]

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), unified per-step `evalDist` coupling.** For *every* oracle query `t` and
every layered state `s`, the `proj2`-projected layered NMA step has the same output/state
distribution as the linked managed step on the projected state. This bundles the four per-step
lemmas (`hproj2_unif`, `hproj2_ro`/`hproj2_ro_ghost_hit`/`hproj2_ro_fresh`, `hproj2_sign`): under
the redesigned `proj2 ((base, ghost), signed) = (baseEmbed (overlayCache base ghost), base)` each
step is an exact equality (the random-oracle and signing steps no longer depend on any reachability
or no-collision side condition), so the coupling holds unconditionally on all of `t`. This is the
per-query hypothesis for the whole-run state-projection `relTriple_simulateQ_run`. -/
lemma hproj2_evalDist (pk : Stmt) (sk : Wit)
    (t : ((unifSpec + (M × Commit →ₒ Chal)) + (M →ₒ Option (Commit × Resp))).Domain)
    (s : NmaGhostState M Commit Chal) :
    𝒟[Prod.map id (proj2 M) <$> (ghostNmaImpl M maxAttempts sim pk sk t).run s] =
      𝒟[(nmaLinkImpl M maxAttempts sim pk t).run (proj2 M s)] := by
  rcases t with (n | mc) | msg
  · exact congrArg _ (hproj2_unif M maxAttempts sim pk sk n s)
  · rcases hgh : s.1.2 mc with _ | v
    · rcases hbh : s.1.1 mc with _ | w
      · exact congrArg _ (hproj2_ro_fresh M maxAttempts sim pk sk mc s hgh hbh)
      · exact congrArg _ (hproj2_ro M maxAttempts sim pk sk mc w s hgh hbh)
    · exact congrArg _ (hproj2_ro_ghost_hit M maxAttempts sim pk sk mc v s hgh)
  · exact hproj2_sign M maxAttempts sim pk sk msg s

/-- **Graph coupling along a function.** If pushing `oa` forward through `F` matches `ob` in
distribution, then `oa` and `ob` are related (as a `RelTriple`) by the graph relation
`fun a b => F a = b`. This is the reverse direction of `evalDist_map_eq_of_relTriple`: the
witnessing coupling is the deterministic coupling `𝒟[oa] >>= fun a => pure (a, F a)`, whose first
marginal is `𝒟[oa]` and whose second marginal is `𝒟[F <$> oa] = 𝒟[ob]`, supported on the graph. -/
private lemma relTriple_graph_of_evalDist_map_eq
    {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [IsUniformSpec spec₁] [IsUniformSpec spec₂]
    {α' σ' : Type} (F : α' → σ')
    (oa : OracleComp spec₁ α') (ob : OracleComp spec₂ σ')
    (h : 𝒟[F <$> oa] = 𝒟[ob]) :
    OracleComp.ProgramLogic.Relational.RelTriple oa ob (fun a b => F a = b) := by
  apply (OracleComp.ProgramLogic.Relational.relTriple_iff_relWP
    (oa := oa) (ob := ob) (R := fun a b => F a = b)).2
  refine ⟨⟨𝒟[oa] >>= fun a => pure (a, F a), ?_, ?_⟩, ?_⟩
  · rw [map_bind]; simp
  · rw [← h, evalDist_map, map_bind]; simp
  · intro z hz
    rcases (mem_support_bind_iff
      (𝒟[oa]) (fun a => (pure (a, F a) : SPMF (α' × σ'))) z).1 hz with ⟨a, _, hz'⟩
    have hzEq : z = (a, F a) := by
      simpa [support_pure, Set.mem_singleton_iff] using hz'
    simp [hzEq]

omit [SampleableType Stmt] in
/-- **Sub-lemma (b), whole-run state projection.** The full layered ghost-tagged NMA run
`(simulateQ ghostNmaImpl (adv.main pk)).run s`, projected by `proj2`, has the same output/state
distribution as the linked managed run `(simulateQ nmaLinkImpl (adv.main pk)).run (proj2 s)`. This
lifts the per-step coupling `hproj2_evalDist` through `relTriple_simulateQ_run` with the state
relation `R s' p := proj2 s' = p` (output-equal, `proj2`-related states), the per-step `RelTriple`
being recovered from the per-step `evalDist`-map equality by the graph coupling
`relTriple_graph_of_evalDist_map_eq`. -/
lemma evalDist_map_run_simulateQ_ghostNmaImpl_proj2 {β : Type} (pk : Stmt) (sk : Wit)
    (oa : OracleComp ((unifSpec + (M × Commit →ₒ Chal)) +
      (M →ₒ Option (Commit × Resp))) β)
    (s : NmaGhostState M Commit Chal) :
    𝒟[Prod.map id (proj2 M) <$> (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) oa).run s] =
      𝒟[(simulateQ (nmaLinkImpl M maxAttempts sim pk) oa).run (proj2 M s)] := by
  -- State relation: `s'` and `p` are related iff `p` is the `proj2`-projection of `s'`.
  have hrel := OracleComp.ProgramLogic.Relational.relTriple_simulateQ_run
    (impl₁ := ghostNmaImpl M maxAttempts sim pk sk)
    (impl₂ := nmaLinkImpl M maxAttempts sim pk)
    (R_state := fun (s' : NmaGhostState M Commit Chal) p => proj2 M s' = p)
    (oa := oa)
    (himpl := fun t s₁ s₂ hs => ?_)
    (s₁ := s) (s₂ := proj2 M s) rfl
  · -- The whole-run `RelTriple` carries `p₁.1 = p₂.1 ∧ proj2 p₁.2 = p₂.2`, i.e. the graph of
    -- `Prod.map id proj2`. Re-express it as a graph relation and extract the `map`-equality.
    have hrel' : OracleComp.ProgramLogic.Relational.RelTriple
        ((simulateQ (ghostNmaImpl M maxAttempts sim pk sk) oa).run s)
        ((simulateQ (nmaLinkImpl M maxAttempts sim pk) oa).run (proj2 M s))
        (fun p₁ p₂ => Prod.map id (proj2 M) p₁ = p₂) :=
      OracleComp.ProgramLogic.Relational.relTriple_post_mono hrel
        (fun p₁ p₂ ⟨h1, h2⟩ => Prod.ext h1 h2)
    have := OracleComp.ProgramLogic.Relational.evalDist_map_eq_of_relTriple
      (f := Prod.map id (proj2 M)) (g := id) hrel'
    simpa using this
  · -- Per-step coupling from the unified per-step `evalDist`-map equality, via the graph coupling.
    subst hs
    refine OracleComp.ProgramLogic.Relational.relTriple_post_mono
      (relTriple_graph_of_evalDist_map_eq (F := Prod.map id (proj2 M))
        ((ghostNmaImpl M maxAttempts sim pk sk t).run s₁)
        ((nmaLinkImpl M maxAttempts sim pk t).run (proj2 M s₁))
        (hproj2_evalDist M maxAttempts sim pk sk t s₁)) ?_
    rintro p₁ p₂ rfl
    exact ⟨rfl, rfl⟩


/-- The managed-RO NMA reduction for Fiat-Shamir with aborts: run the CMA adversary,
forwarding uniform queries, answering live hash queries through a managed cache, and
answering signing queries with the simulator loop of `simSignBody` (programming the
accepted transcript's challenge into the managed cache). Returns the forgery together
with the managed cache, in the interface of `SignatureAlg.managedRoNmaAdv`. -/
noncomputable def simulatedNmaAdv :
    SignatureAlg.managedRoNmaAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts) where
  main pk :=
    let spec := unifSpec + (M × Commit →ₒ Chal)
    let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
    let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
      fun n => fwd (.inl n)
    let roSim : QueryImpl (M × Commit →ₒ Chal)
        (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
      let cache ← get
      match cache (.inr mc) with
      | some v => pure v
      | none => do
          let v ← fwd (.inr mc)
          modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
    let sigSim : QueryImpl (M →ₒ Option (Commit × Resp))
        (StateT spec.QueryCache (OracleComp spec)) := fun msg => do
      let r ← simulateQ unifSim (firstSome (sim pk) maxAttempts)
      match r with
      | some (w, c, z) =>
          modifyGet fun cache => (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
      | none => pure none
    -- Run the inner CMA adversary under the managed simulation, then erase the
    -- forgery's own verification point from the returned cache (Option B). The
    -- with-aborts `verify pk msg (some (w', z))` issues exactly one hash query, at
    -- `(msg, w')`; clearing that entry makes `withCacheOverlay advCache verify` miss
    -- there and fall through to the live oracle, so the managed-RO experiment agrees
    -- with the plain EUF-NMA verification on *every* forgery. In particular a replayed
    -- signed `(msg, w')` no longer wins through the programmed challenge, which is what
    -- makes the bridge to `eufNmaAdv.advantage` sound. Other programmed entries sit at
    -- different points and are never read by `verify`.
    (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅ >>= fun result =>
      let ((msg, σ), cache) := result
      let advCache : spec.QueryCache :=
        match σ with
        | some (w', _) => Function.update cache (Sum.inr (msg, w')) none
        | none => cache
      pure ((msg, σ), advCache)

omit [SampleableType Stmt] in
/-- **Nested-simulation fusion for the managed NMA run.** The managed reduction runs the
common adversary `adv.main pk` under the inner managed handler `nmaOuterImpl pk` threading the
inner cache (`StateT spec.QueryCache (OracleComp spec)`), then `.run ∅` re-simulates the
residual live queries under the outer runtime handler `nmaInnerImpl` (`unifFwdImpl +
randomOracle`) threading the outer cache. By `QueryImpl.Stateful.simulateQ_link_run` this
two-layer nesting is a single simulation of the *linked* handler `nmaLinkImpl pk =
(nmaOuterImpl pk).link nmaInnerImpl` over the product cache, up to the canonical `linkReshape`
regrouping of the final state. This collapses the explicit `.run ∅` boundary into a single
`simulateQ` whose state is the genuine `(inner managed cache, outer runtime cache)` pair the
per-step coupling projects onto. -/
lemma managedRun_eq_link_run (pk : Stmt) :
    letI spec := unifSpec + (M × Commit →ₒ Chal)
    (simulateQ (nmaLinkImpl M maxAttempts sim pk) (adv.main pk)).run (∅, ∅) =
      (QueryImpl.Stateful.Frame.prod spec.QueryCache
          ((M × Commit →ₒ Chal).QueryCache)).linkReshape (∅, ∅) <$>
        (simulateQ (nmaInnerImpl M)
          ((simulateQ (nmaOuterImpl M maxAttempts sim pk)
            (adv.main pk)).run ∅)).run ∅ := by
  exact (QueryImpl.Stateful.simulateQ_link_run _ _ (adv.main pk) ∅ ∅)

omit [SampleableType Stmt] [SampleableType Chal] in
/-- If a cache misses at the forgery's verification point `Sum.inr (msg, w')`, the overlay
verification of `FiatShamirWithAbort.verify pk msg (some (w', z))` agrees with the plain
live verification: the single query at `Sum.inr (msg, w')` misses and is forwarded live.
The `none` case is verification-free, so it is trivially overlay-insensitive. -/
lemma withCacheOverlay_verify_eq_of_miss
    (cache : (unifSpec + (M × Commit →ₒ Chal)).QueryCache) (pk : Stmt)
    (msg : M) (σ : Option (Commit × Resp))
    (hmiss : ∀ w' z, σ = some (w', z) → cache (Sum.inr (msg, w')) = none) :
    withCacheOverlay cache
        ((FiatShamirWithAbort (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
          ids hr M maxAttempts).verify pk msg σ) =
      (FiatShamirWithAbort (m := OracleComp (unifSpec + (M × Commit →ₒ Chal)))
        ids hr M maxAttempts).verify pk msg σ := by
  cases σ with
  | none => simp only [FiatShamirWithAbort, withCacheOverlay_pure]
  | some wz =>
      obtain ⟨w', z⟩ := wz
      have hm : cache (Sum.inr (msg, w')) = none := hmiss w' z rfl
      change withCacheOverlay _
          ((query (Sum.inr (msg, w')) :
            OracleComp (unifSpec + (M × Commit →ₒ Chal))
              ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inr (msg, w')))) >>=
            fun c => pure (ids.verify pk w' c z)) =
        (query (Sum.inr (msg, w')) :
            OracleComp (unifSpec + (M × Commit →ₒ Chal))
              ((unifSpec + (M × Commit →ₒ Chal)).Range (Sum.inr (msg, w')))) >>=
            fun c => pure (ids.verify pk w' c z)
      rw [withCacheOverlay_bind_pure, bind_pure_comp]
      congr 1
      exact withCacheOverlay_query_miss _ (Sum.inr (msg, w')) hm

omit [SampleableType Stmt] in
/-- **Verify-tail pointwise split** (the per-forgery content of the NMA bridge). On a common
ghost-tagged output state `((base, ghost), signed)` satisfying the ghost-domain invariant
(every ghost point's message is signed), the hybrid verification-and-freshness continuation
`hybridVerifyCont` on the overlay cache is bounded by the managed overlay verification on the
base cache. On `msg ∈ signed` the freshness conjunct zeroes the left
(`probOutput_true_hybridVerifyCont_of_mem`); on a fresh forgery `msg ∉ signed` the invariant
makes the ghost layer miss at every `(msg, w)`, so the overlay agrees with the base cache
(`hybridVerifyCont_cache_congr`), the Option-B post-processing makes `withCacheOverlay` miss
its own verification point (`withCacheOverlay_verify_eq_of_miss`), and the two tails coincide. -/
lemma probOutput_hybridVerifyCont_le_managed_verify (pk : Stmt)
    (ms : M × Option (Commit × Resp)) (base ghost : (M × Commit →ₒ Chal).QueryCache)
    (signed : List M)
    (hinv : ∀ q : M × Commit, ghost q ≠ none → q.1 ∈ signed) :
    Pr[= true | hybridVerifyCont ids hr M maxAttempts pk
        (ms, (overlayCache M base ghost, signed))] ≤
      Pr[= true | (fun x : Bool × _ => x.1) <$>
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          (withCacheOverlay
            (match ms.2 with
              | some (w', _) => Function.update (baseEmbed M (overlayCache M base ghost))
                  (Sum.inr (ms.1, w')) none
              | none => baseEmbed M (overlayCache M base ghost))
            ((FiatShamirWithAbort ids hr M maxAttempts).verify pk ms.1 ms.2))).run base] := by
  obtain ⟨msg, σ⟩ := ms
  by_cases hmem : msg ∈ signed
  · rw [probOutput_true_hybridVerifyCont_of_mem ids hr M maxAttempts pk (msg, σ)
      (overlayCache M base ghost) signed hmem]
    exact zero_le'
  · rw [withCacheOverlay_verify_eq_of_miss ids hr M maxAttempts _ pk msg σ
        (by intro w' z hσ; simp [hσ]),
      hybridVerifyCont_cache_congr ids hr M maxAttempts pk (msg, σ)
        (overlayCache M base ghost) base signed
        (fun w => overlayCache_apply_ghost_none (M := M) base
          (by by_contra h; exact hmem (hinv (msg, w) h)))]
    refine le_of_eq ?_
    simp only [hybridVerifyCont, hmem, not_false_eq_true, decide_true, Bool.true_and,
      StateT.run', bind_pure]
    rfl

omit [SampleableType Stmt] in
/-- **State-coupling for the NMA bridge** (genuine two-layer content). At a fixed key pair
the single-cache hybrid run of `hybridExpAtKey`, *followed by its verification-and-freshness
tail* `hybridVerifyCont`, is bounded by the run-normal-form of the managed-RO NMA
experiment: the managed-cache run of `simulatedNmaAdv` (re-simulated under the runtime's
outer `randomOracle`), followed by overlay verification.

The two presentations run the *same* adversary `adv.main pk` but thread the random-oracle
cache through genuinely different layers:

* the **hybrid** (`impl₁ := hybridBaseImpl + hybridSignImpl simSignBody`) keeps a *single*
  cache `(cache, signed)`, into which both live RO reads (`randomOracle`) and the signing
  simulation's accepted-transcript programming (`simSignBody` via `signProgramCont`) write;
* the **managed reduction** (`simulatedNmaAdv.main`) keeps an *inner managed* cache threaded
  by `roSim`/`sigSim`, whose live `fwd` reads are resolved by the runtime's *separate outer*
  `randomOracle` cache. `simulateQ_compose` (`∘ₛ`) does not collapse these two layers because
  the inner `.run ∅` boundary turns `roSim`/`fwd` misses into live queries answered by the
  outer oracle.

The coupling claim is that the *overlay* of the inner managed cache onto the outer runtime
cache reproduces the single hybrid cache throughout the run (a state-projection in the sense
of `OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'`), and that the signed-message list
matches the set of points the managed simulation programmed (a cache invariant in the style
of `fsAbortSignLoop_cache_invariant`). On `msg ∈ signed` the freshness conjunct kills the
left side (`probOutput_true_hybridVerifyCont_of_mem`); on fresh forgeries the
`withCacheOverlay` verification agrees with the live verification at the verification point
(`withCacheOverlay_verify_eq_of_miss`, since the managed point at `(msg, w')` carries the
programmed challenge that equals the hybrid's cached value, while the freshness check rules
out a stale read). Hence the per-forgery success of the hybrid tail is at most that of the
overlay verification, and the bound follows. -/
lemma hybridSimRun_le_managedRun_verify (pk : Stmt) (sk : Wit) :
    Pr[= true | (simulateQ
          (hybridBaseImpl (Commit := Commit) (Chal := Chal) M +
            hybridSignImpl M (simSignBody M maxAttempts sim pk sk))
          (adv.main pk)).run (∅, []) >>= hybridVerifyCont ids hr M maxAttempts pk] ≤
      Pr[= true | (fun x : Bool × _ => x.1) <$> do
        let p ← (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pk)).run ∅
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
            (randomOracle : QueryImpl (M × Commit →ₒ Chal)
              (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
          (withCacheOverlay p.1.2 ((FiatShamirWithAbort ids hr M maxAttempts).verify
            pk p.1.1.1 p.1.1.2))).run p.2] := by
  -- Step 1 (banked, axiom-clean): collapse the explicit `.run ∅` re-simulation boundary on
  -- the RHS. Distributing the outer `simulateQ` over `simulatedNmaAdv`'s post-processing bind
  -- (`simulateQ_bind`/`StateT.run_bind`) exposes the nested managed run
  --   `(simulateQ (unifFwd+ro) ((simulateQ ((unifSim+roSim)+sigSim) (adv.main pk)).run ∅)).run ∅`,
  -- which `managedRun_eq_link_run` rewrites to the canonical `linkReshape` of a *single*
  -- linked simulation `(simulateQ (outer.link inner) (adv.main pk)).run (∅, ∅)` over the
  -- product cache `(inner managed cache, outer runtime cache)`. After this rewrite the RHS is
  -- a single `simulateQ` whose state is genuinely the inner/outer cache pair, so the coupling
  -- to the hybrid is a plain `map_run_simulateQ_eq_of_query_map_eq_inv'` state-projection (no
  -- nesting). The fusion lemma `managedRun_eq_link_run` is proven and axiom-clean.
  --
  -- RESIDUAL SUBGOAL (the genuinely hard, still-open content): the state-projection coupling
  -- of `impl₁ := hybridBaseImpl + hybridSignImpl simSignBody` (single state `(reCache, signed)
  -- : (M × Commit →ₒ Chal).QueryCache × List M`) against `impl₂ := outer.link inner` (state
  -- `(innerCache, outerCache) : spec.QueryCache × (M × Commit →ₒ Chal).QueryCache`), followed
  -- by the verify-tail split.
  --
  -- DESIGN OBSTRUCTION FOUND (corrects the original `proj` recipe). A per-step replay of both
  -- handlers shows the linked caches evolve as:
  --   * `outerCache` accumulates *only live RO reads* (`roSim` forwards inner misses to `fwd`,
  --     re-simulated by `inner`'s `randomOracle`, which writes the outer layer); signing's
  --     `sigSim` programs the *inner* layer only and never forwards to the outer oracle;
  --   * `innerCache` accumulates *both* live RO reads *and* the signing-programmed points.
  -- Hence `reCache = innerCache` and `overlayCache outerCache innerCache = reCache`
  -- throughout — matching the docstring's overlay claim. The problem is that the verifying
  -- direction of `map_run_simulateQ_eq_of_query_map_eq_inv'` requires `proj` to be a *total
  -- function of the hybrid state* `(reCache, signed)` whose value reproduces the linked state
  -- pair *exactly* (not just up to overlay): `(impl₂ t).run (proj s) = Prod.map id proj <$>
  -- (impl₁ t).run s`. But `outerCache = reCache ∖ {signing-only-programmed points}` is **not a
  -- function of `(reCache, signed)`**: a point `(msg, w)` with `msg ∈ signed` may have entered
  -- `reCache` either by a live RO read (then it is in `outerCache`) or by `signProgramCont`
  -- (then it is *absent* from `outerCache`), and the current hybrid state records no flag
  -- distinguishing the two. Defining `proj.outerCache := reCache` fails on the signing step
  -- (hybrid writes the programmed point to `reCache`, so `proj.outerCache` would gain it, but
  -- the linked `outerCache` does not), and the restricted-by-`signed` choice fails on live
  -- reads at signed messages (those *are* in the linked `outerCache`). The split therefore
  -- depends on per-query programming history that neither the hybrid `(reCache, signed)` nor
  -- the linked cache pair records on its own — so the coupling is *not* a single
  -- `map_run_simulateQ_eq_of_query_map_eq_inv'` over the existing states.
  --
  -- RESOLUTION (not yet built; ~150–250 lines of new infrastructure). Run the hybrid (or the
  -- linked managed handler) on an *enriched, layered* cache state that explicitly tags each
  -- entry as live-read vs signing-programmed — the same `overlayCache`/ghost-layer device
  -- already used for the Prog→Trans hop in `GhostBodies` (`ghostHybridImpl`, `GhostState`,
  -- `run_ghostSignBody_overlay`/`_fst`). On that layered state the partition *is* a function
  -- of the state, both projection directions (`overlay`-to-hybrid and `forget`-to-managed) are
  -- per-step state projections, and `map_run_simulateQ_eq_of_query_map_eq_inv'` applies. The
  -- verify-tail then splits on `result.1.1 ∈ signed` exactly as in the original recipe:
  -- `probOutput_true_hybridVerifyCont_of_mem` zeroes the LHS on `msg ∈ signed`, while on fresh
  -- forgeries `withCacheOverlay_verify_eq_of_miss` + `hybridVerifyCont_cache_congr` align the
  -- overlay verification with the live verification. The fusion (Step 1) and the verify-tail
  -- toolkit are in place; the open content is the layered-state projection.
  --
  -- STEP 1 (executed below, axiom-clean): the mechanical link-fusion plumbing. Distributing
  -- `simulateQ_bind`/`StateT.run_bind` over `simulatedNmaAdv.main`'s Option-B post-processing
  -- bind exposes the bare nested managed run, and `managedRun_eq_link_run` rewrites it to the
  -- single linked simulation `(simulateQ (outer.link inner) (adv.main pk)).run (∅, ∅)`.
  simp only [simulatedNmaAdv, simulateQ_bind, StateT.run_bind, bind_assoc]
  -- The RHS is now `(fun x => x.1) <$> do let p ← (simulateQ (unifFwd+ro)
  --   ((simulateQ ((unifSim+roSim)+sigSim) (adv.main pk)).run ∅)).run ∅; (Option-B post)…`,
  -- with the bare nested managed run exposed. `managedRun_eq_link_run` equates this nested
  -- run (modulo the canonical `linkReshape <$> _` regrouping of the final state) with the
  -- single linked simulation `(simulateQ (outer.link inner) (adv.main pk)).run (∅, ∅)`.
  --
  -- REMAINING SUBGOAL (the genuine still-open content). With the nested boundary exposed, the
  -- bound is the state-projection coupling described above: a layered ghost-tagged handler that
  -- partitions each cache point as live-read (base layer) vs signing-programmed (ghost layer),
  -- projecting (a) by `overlayCache` to the single hybrid cache and (b) by the
  -- `randomOracle_run_eq_roStep` round-trip to the linked (inner,outer) pair under the invariant
  -- "every ghost-tagged point's msg ∈ signed", then (c) the verify-tail split on `msg ∈ signed`
  -- (`probOutput_true_hybridVerifyCont_of_mem`, `withCacheOverlay_verify_eq_of_miss`,
  -- `hybridVerifyCont_cache_congr`). The fusion `simp only` above is the executed, axiom-clean
  -- Step 1; the layered-state projection is the open content.
  --
  -- BANKED (sub-lemma (a), axiom-clean, `GhostBodies.lean`). The layered ghost-tagged handler
  -- is now built: `ghostNmaImpl` over the state `((baseCache, ghostCache), signed)` (abbrev
  -- `NmaGhostState`), with `simGhostSignBody`/`ghostSignProgramCont` writing the accepted
  -- transcript to the ghost layer and the base oracles writing live RO reads to the base layer.
  -- The overlay projection back to the plain single-cache hybrid is proven:
  --   `ghostNmaImpl_proj_hybrid` (per step) and
  --   `map_run_simulateQ_ghostNmaImpl_overlay`/`_empty` (full run), via
  --   `OracleComp.map_run_simulateQ_eq_of_query_map_eq` with
  --   `proj ((base, ghost), signed) = (overlayCache base ghost, signed)`.
  -- Hence the hybrid LHS equals `Pr[= true | (overlay-projected ghostNmaImpl run) >>= …]`.
  --
  -- EXACT OPEN RESIDUAL (sub-lemma (b), not landed; ~2-3 weeks). Couple the *same* layered run
  -- `(simulateQ (ghostNmaImpl …) (adv.main pk)).run ((∅,∅), [])` to the linked managed run
  -- `(simulateQ (outer.link inner) (adv.main pk)).run (∅, ∅)` (from `managedRun_eq_link_run`)
  -- under the projection `proj₂ ((base, ghost), signed) = (baseEmbed base, overlayCache base
  -- ghost)` onto the linked `(outerCache : spec.QueryCache, innerCache : (M×Commit→ₒChal).
  -- QueryCache)` pair (outer = live-read layer = base, inner = full hybrid cache = overlay).
  -- The per-step `hproj` linchpin is NOT a primitive-query projection against `outer.link inner`:
  -- by `linkWith_apply_run`, each `(outer.link inner) t` step is itself a *nested*
  -- `simulateQ inner ((outer t).run …)`, where `outer t` (roSim/sigSim) is a multi-query
  -- composite — roSim does an inner cache lookup then forwards a miss to `fwd` (re-simulated by
  -- `inner`'s `randomOracle`, the `randomOracle_run_eq_roStep` round-trip), and sigSim runs a
  -- whole `simulateQ unifSim (firstSome (sim pk) maxAttempts)`. So (b) requires coupling
  -- `ghostNmaImpl` against the *nested-simulation* form of the managed handler step-by-step,
  -- under the ghost-domain invariant "every ghost point's msg ∈ signed" (cf.
  -- `ghostHybridImpl_preserves_signed_inv` for the sibling hop), so that on the RO step the
  -- live read writes the base layer and outer cache identically, while the signing step's ghost
  -- write matches the inner cache's `cacheQuery (.inr (msg, w)) c` and never touches the outer.
  -- This is the genuine multi-week content; (a) and the verify-tail toolkit (c) are in place.
  --
  -- BANKED toward (b) (axiom-clean, `GhostBodies.lean`). The ghost-domain *gate* and the left
  -- component of `proj₂` are now built and proven:
  --   * `ghostNmaImpl_preserves_signed_inv` — the invariant "every ghost-layer point's msg ∈
  --     signed" is preserved by every `ghostNmaImpl` step (NMA analogue of
  --     `ghostHybridImpl_preserves_signed_inv`), backed by the new support fact
  --     `simGhostSignBody_support_ghost` (the signing body only writes ghost points whose msg is
  --     the signed message). This is exactly the `inv` to feed
  --     `map_run_simulateQ_eq_of_query_map_eq_inv'`.
  --   * `baseEmbed` (+ `baseEmbed_inr`/`baseEmbed_inl`/`baseEmbed_cacheQuery`) — the embedding
  --     of a base RO cache (keyed by `M × Commit`) into the outer runtime cache (keyed by the
  --     sum spec), i.e. the left component of `proj₂ ((base,ghost),signed) = (baseEmbed base,
  --     overlayCache base ghost)`; `baseEmbed_cacheQuery` provides the RO-step algebra
  --     `baseEmbed (base.cacheQuery mc v) = (baseEmbed base).cacheQuery (.inr mc) v`.
  -- DONE: the local `outer`/`inner`/`roSim`/`sigSim`/`unifSim` lets of
  -- `simulatedNmaAdv`/`managedRun_eq_link_run` are now top-level handlers `nmaOuterImpl`,
  -- `nmaInnerImpl`, and `nmaLinkImpl := (nmaOuterImpl …).link (nmaInnerImpl …)`, so the linked
  -- handler is nameable; `managedRun_eq_link_run` is re-expressed in terms of them and stays
  -- axiom-clean. The per-step coupling is stated as
  --   `hproj₂ : Prod.map id proj₂ <$> (ghostNmaImpl t).run s
  --              = (nmaLinkImpl M maxAttempts sim pk t).run (proj₂ s)`
  -- with `proj₂ ((base, ghost), signed) = (baseEmbed base, overlayCache base ghost)`, split into
  -- `hproj2_unif`, `hproj2_ro`, `hproj2_ro_fresh` (all PROVEN, axiom-clean) and `hproj2_sign`.
  --
  -- R21 RESOLUTION (the per-step sign equality is now PROVEN — UNCONDITIONALLY). The earlier
  -- obstruction (the sign step is not a per-step state function under `proj₂ = (baseEmbed base,
  -- overlayCache base ghost)`) is fixed by *redesigning* `proj₂` to
  -- `proj2 ((base, ghost), signed) = (baseEmbed (overlayCache base ghost), base)` — inner managed
  -- cache = full hybrid overlay (live reads + sign points), outer runtime cache = live-read base
  -- layer only. Under this projection ALL per-step couplings are exact unconditional equalities
  -- (`hproj2_unif`, `hproj2_ro`, `hproj2_ro_ghost_hit`, `hproj2_ro_fresh`, `hproj2_sign`), bundled
  -- into `hproj2_evalDist` and lifted to the whole run by
  -- `evalDist_map_run_simulateQ_ghostNmaImpl_proj2` (via `relTriple_simulateQ_run` + the graph
  -- coupling `relTriple_graph_of_evalDist_map_eq`). The `signLiveCollision` reframe is no longer
  -- needed: the redesigned projection carries the sign point in the inner slot whether or not it
  -- coincides with a prior live read.
  --
  -- ASSEMBLY (the verify-tail split, executed below). With (a)
  -- `map_run_simulateQ_ghostNmaImpl_overlay_empty` and (b)
  -- `evalDist_map_run_simulateQ_ghostNmaImpl_proj2` both PROVEN, the hybrid LHS run and the
  -- linked managed RHS run are both projections of the *same* layered ghost-tagged run
  -- `(simulateQ ghostNmaImpl (adv.main pk)).run ((∅,∅), [])`. The two verify tails are aligned on
  -- this common run by `probOutput_hybridVerifyCont_le_managed_verify` — on `msg ∈ signed` the
  -- freshness conjunct zeroes the hybrid side (`probOutput_true_hybridVerifyCont_of_mem`), and on
  -- fresh forgeries the overlay verification agrees with the live verification
  -- (`withCacheOverlay_verify_eq_of_miss`, `hybridVerifyCont_cache_congr`), gated by the whole-run
  -- ghost-domain invariant `ghostNmaImpl_run_signed_inv`. The `linkReshape` / Option-B
  -- post-processing regrouping is threaded by `managedRun_eq_link_run` + `bind_map_left`.
  --
  -- Reduce the Option-B post-processing `pure` (re-simulated under `nmaInner`) to its value, and
  -- pull the outer `(fun x => x.1) <$> _` past the head bind. The RHS is now `nestedManaged >>= K`
  -- with `K a = (fun x => x.1) <$> (simulateQ nmaInner (withCacheOverlay (advCache a)
  -- (verify pk a.1.1.1 a.1.1.2))).run a.2`.
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, map_bind]
  -- The managed verify tail, expressed as a function of the *value × linked cache pair*. By
  -- `proj2` it is the layered-run tail; by `linkReshape` it is the nested managed tail.
  set RHSverify : (M × Option (Commit × Resp)) ×
      ((unifSpec + (M × Commit →ₒ Chal)).QueryCache × (M × Commit →ₒ Chal).QueryCache) →
      ProbComp Bool :=
    fun p => (fun x : Bool × _ => x.1) <$>
      (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) +
          (randomOracle : QueryImpl (M × Commit →ₒ Chal)
            (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp)))
        (withCacheOverlay
          (match p.1.2 with
            | some (w', _) => Function.update p.2.1 (Sum.inr (p.1.1, w')) none
            | none => p.2.1)
          ((FiatShamirWithAbort ids hr M maxAttempts).verify pk p.1.1 p.1.2))).run p.2.2
    with hRHSverify
  -- LHS: rewrite the plain hybrid run as the overlay projection of the layered ghost run (a),
  -- and push the projection through the bind (`map_bind`).
  rw [← map_run_simulateQ_ghostNmaImpl_overlay_empty M maxAttempts sim pk sk (adv.main pk),
    bind_map_left]
  -- RHS: fold the unfolded handlers back to `nmaOuterImpl`/`nmaInnerImpl`, regroup the nested
  -- managed run by `managedRun_eq_link_run` into `linkRun`, then transport `linkRun`'s
  -- distribution back to the layered ghost run by sub-lemma (b).
  have hRHS :
      Pr[= true | (simulateQ (nmaInnerImpl M)
            ((simulateQ (nmaOuterImpl M maxAttempts sim pk) (adv.main pk)).run ∅)).run ∅ >>=
          fun a => RHSverify (a.1.1, (a.1.2, a.2))] =
        Pr[= true | (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) (adv.main pk)).run
            ((∅, ∅), []) >>= fun g => RHSverify (g.1, proj2 M g.2)] := by
    -- The ghost-side tail factors through `Prod.map id proj2`; the nested-side tail factors
    -- through `linkReshape`. Rewriting both tails as `RHSverify <$> (the projected head)` via
    -- `bind_map_left` lets sub-lemma (b) (`proj2 <$> ghostRun =𝒟 linkRun`) and the fusion
    -- (`linkRun = linkReshape <$> nested`) line the two heads up.
    have hproj2_empty : proj2 M (((∅ : (M × Commit →ₒ Chal).QueryCache),
        (∅ : (M × Commit →ₒ Chal).QueryCache)), ([] : List M)) = (∅, ∅) := by
      simp only [proj2, overlayCache_empty]
      exact congrArg (·, ∅) (baseEmbed_empty M)
    have hghost :
        (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) (adv.main pk)).run ((∅, ∅), []) >>=
            (fun g => RHSverify (g.1, proj2 M g.2)) =
          (Prod.map id (proj2 M) <$>
              (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) (adv.main pk)).run
                ((∅, ∅), [])) >>= RHSverify := by
      rw [bind_map_left]; rfl
    have hnested :
        (simulateQ (nmaInnerImpl M)
              ((simulateQ (nmaOuterImpl M maxAttempts sim pk) (adv.main pk)).run ∅)).run ∅ >>=
            (fun a => RHSverify (a.1.1, (a.1.2, a.2))) =
          ((QueryImpl.Stateful.Frame.prod (unifSpec + (M × Commit →ₒ Chal)).QueryCache
                ((M × Commit →ₒ Chal).QueryCache)).linkReshape (∅, ∅) <$>
              (simulateQ (nmaInnerImpl M)
                ((simulateQ (nmaOuterImpl M maxAttempts sim pk) (adv.main pk)).run ∅)).run ∅) >>=
            RHSverify := by
      rw [bind_map_left]; rfl
    rw [hghost, hnested]
    -- Reduce to the head-distribution equality, then bind with `RHSverify`.
    have hhead :
        𝒟[Prod.map id (proj2 M) <$>
            (simulateQ (ghostNmaImpl M maxAttempts sim pk sk) (adv.main pk)).run ((∅, ∅), [])] =
          𝒟[(QueryImpl.Stateful.Frame.prod (unifSpec + (M × Commit →ₒ Chal)).QueryCache
                ((M × Commit →ₒ Chal).QueryCache)).linkReshape (∅, ∅) <$>
              (simulateQ (nmaInnerImpl M)
                ((simulateQ (nmaOuterImpl M maxAttempts sim pk) (adv.main pk)).run ∅)).run ∅] := by
      rw [evalDist_map_run_simulateQ_ghostNmaImpl_proj2 M maxAttempts sim
        pk sk (adv.main pk) ((∅, ∅), []), hproj2_empty,
        managedRun_eq_link_run ids hr M maxAttempts sim adv pk]
    refine OracleComp.probOutput_congr rfl ?_
    rw [evalDist_bind, evalDist_bind, hhead]
  -- Assemble: the goal RHS is `nestedManaged >>= K` (`= hRHS`'s LHS, defeq), so rewrite to the
  -- common ghost run, then `probOutput_bind_mono` against the pointwise verify-tail split, gated
  -- by the whole-run ghost-domain invariant.
  refine le_trans ?_ (le_of_eq hRHS.symm)
  refine probOutput_bind_mono fun a ha => ?_
  obtain ⟨av, ⟨base, ghost⟩, signed⟩ := a
  exact probOutput_hybridVerifyCont_le_managed_verify ids hr M maxAttempts pk av base ghost signed
    (fun q hq => ghostNmaImpl_run_signed_inv M maxAttempts sim pk sk (adv.main pk) _ ha q hq)

omit [SampleableType Stmt] in
/-- **Per-key cache-overlay invariant** (core of the NMA bridge): at a fixed key pair the
simulated single-cache hybrid (with the freshness check) is bounded by the run-normal-form
of the managed-RO NMA experiment — the managed-cache run of `simulatedNmaAdv` followed by
overlay verification, all under the runtime's `randomOracle` layer.

This is the genuine distributional content of `probOutput_hybridExp_sim_le_managedRoNmaExp`:
the inner managed cache threaded by `roSim`/`sigSim` together with the runtime's outer
`randomOracle` layer reproduces the single-cache hybrid run of `hybridExpAtKey`, and on
fresh forgeries the `withCacheOverlay` verification agrees with the live oracle at the
verification point (a cache invariant in the style of `fsAbortSignLoop_cache_invariant`:
every entry programmed by the signing simulation has its message recorded in the signed
list, so the freshness conjunct can only decrease the left-hand side). -/
lemma hybridExp_sim_le_managedRun_perKey
    (ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp))
    (hro : ro = randomOracle) (pk : Stmt) (sk : Wit) :
    Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
        (simSignBody M maxAttempts sim pk sk) pk] ≤
      Pr[= true | (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
        ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pk >>= fun result =>
          withCacheOverlay result.2
            ((FiatShamirWithAbort ids hr M maxAttempts).verify
              pk result.1.1 result.1.2))).run' ∅] := by
  subst hro
  -- Put the hybrid LHS into run-normal-form (`run` of the hybrid handler on `adv.main pk`
  -- followed by the verify-and-freshness tail `hybridVerifyCont`).
  rw [hybridExpAtKey_eq_run_bind]
  -- Put the managed RHS into run-normal-form: `simulateQ_bind` distributes the outer RO
  -- simulation over the managed run and the overlay verification, and `StateT.run'`/`run`
  -- exposes the `(forgery, runtimeCache)` bind as a `ProbComp` bind whose final value is the
  -- forgery's verification bit (`pure p.1`).
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  exact hybridSimRun_le_managedRun_verify ids hr M maxAttempts sim adv pk sk

omit [SampleableType Stmt] in
/-- NMA bridge: the success probability of the simulated hybrid (averaged over key
generation, with the freshness check) is at most the success probability of
`simulatedNmaAdv` in the managed-RO NMA experiment.

Distributional content: (i) the single-cache-layer hybrid run coincides with the
managed-cache run of `simulatedNmaAdv` followed by overlay verification
(`withCacheOverlay`), and (ii) by a cache invariant in the style of
`fsAbortSignLoop_cache_invariant`, every entry programmed by the signing simulation has
its message recorded in the signed list, so on fresh forgeries the overlay agrees with
the live oracle at the verification point and the freshness conjunct can only decrease
the left-hand side. A hash-query-bound transfer in the style of
`FiatShamir.simulatedNmaAdv_hashQueryBound` (the loop issues no live hash queries)
should accompany this lemma when the downstream consumer needs NMA query bounds. -/
lemma probOutput_hybridExp_sim_le_managedRoNmaExp :
    Pr[= true | do
        let (pk, sk) ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim pk sk) pk] ≤
      Pr[= true | SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv)] := by
  classical
  -- Abbreviation for the runtime random-oracle simulator.
  set ro : QueryImpl (M × Commit →ₒ Chal)
      (StateT ((M × Commit →ₒ Chal).QueryCache) ProbComp) := randomOracle with hro
  -- Normal form of the managed-RO NMA experiment: the runtime's `withStateOracle`
  -- semantics unfolds to a single `simulateQ … |>.run' ∅`, and the lifted key
  -- generation pulls out as an ordinary `ProbComp` bind via `roSim.run'_liftM_bind`.
  have hRHS : Pr[= true | SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv)] =
      Pr[= true | hr.gen >>= fun pksk =>
        (simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
          ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pksk.1 >>= fun result =>
            withCacheOverlay result.2
              ((FiatShamirWithAbort ids hr M maxAttempts).verify
                pksk.1 result.1.1 result.1.2))).run' ∅] := by
    unfold SignatureAlg.managedRoNmaExp
    -- Expose the bundled `withStateOracle` semantics as a run-normal-form ProbComp.
    change Pr[= true | 𝒟[(simulateQ (unifFwdImpl (M × Commit →ₒ Chal) + ro)
        (do
          let (pk, _) ← (FiatShamirWithAbort ids hr M maxAttempts).keygen
          let result ← (simulatedNmaAdv ids hr M maxAttempts sim adv).main pk
          withCacheOverlay result.2
            ((FiatShamirWithAbort ids hr M maxAttempts).verify
              pk result.1.1 result.1.2))).run' ∅]] = _
    -- `keygen = monadLift hr.gen`; pull it out of the simulation.
    rw [show (FiatShamirWithAbort ids hr M maxAttempts).keygen =
      (liftM hr.gen : OracleComp (unifSpec + (M × Commit →ₒ Chal)) (Stmt × Wit)) from rfl]
    rw [simulateQ_bind, roSim.run'_liftM_bind]
    rfl
  rw [hRHS]
  -- Reduce to a per-key statement under the shared `hr.gen` prefix.
  refine probOutput_bind_mono fun pksk _ => ?_
  -- Per-key core: the simulated hybrid (with the freshness check) is bounded by the
  -- managed-cache run of `simulatedNmaAdv` followed by overlay verification. This is the
  -- cache-overlay invariant: the inner managed cache `roSim` plus the runtime's outer
  -- `randomOracle` layer reproduces the single-cache hybrid, and on fresh forgeries the
  -- overlay agrees with the live oracle at the verification point.
  obtain ⟨pk, sk⟩ := pksk
  exact hybridExp_sim_le_managedRun_perKey ids hr M maxAttempts sim adv ro hro pk sk

/-! ## Bridge to the plain EUF-NMA interface

Option B makes `simulatedNmaAdv` discard the forgery's own verification point from the
returned managed cache. The single hash query issued by `FiatShamirWithAbort.verify`
therefore always *misses* in the overlay and falls through to the live oracle, so the
overlay verification coincides — as an `OracleComp` — with the plain verification. This
collapses the managed-RO NMA experiment onto the plain EUF-NMA experiment of the
cache-forgetting adversary `simulatedEufNmaAdv`, making the bound
`Pr[managedRoNmaExp simulatedNmaAdv] ≤ simulatedEufNmaAdv.advantage` sound. -/

/-- The plain EUF-NMA adversary underlying `simulatedNmaAdv`: run the same managed
simulation of the CMA adversary, but forget the returned cache and verify in the plain
random-oracle model. By Option B (`withCacheOverlay_verify_eq_of_miss`) the managed-RO NMA
experiment of `simulatedNmaAdv` coincides with the plain EUF-NMA experiment of this
adversary. -/
noncomputable def simulatedEufNmaAdv :
    SignatureAlg.eufNmaAdv
      (FiatShamirWithAbort
        (m := OracleComp (unifSpec + (M × Commit →ₒ Chal))) ids hr M maxAttempts) where
  main pk := Prod.fst <$> (simulatedNmaAdv ids hr M maxAttempts sim adv).main pk

omit [SampleableType Stmt] in
/-- **Soundness of the managed-RO → plain EUF-NMA bridge** (Option B). The managed-RO NMA
success probability of `simulatedNmaAdv` equals the plain EUF-NMA success probability of
`simulatedEufNmaAdv`. The Option B post-processing erases the forgery's own verification
point from the returned cache, so `withCacheOverlay` agrees with the plain live verifier
on every forgery (`withCacheOverlay_verify_eq_of_miss`); in particular a replayed signed
forgery no longer wins through a programmed challenge. -/
lemma managedRoNmaExp_simulatedNmaAdv_eq_eufNmaExp :
    SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv) =
      SignatureAlg.eufNmaExp (runtime M)
        (simulatedEufNmaAdv ids hr M maxAttempts sim adv) := by
  unfold SignatureAlg.managedRoNmaExp SignatureAlg.eufNmaExp
  refine congrArg (runtime M).evalDist ?_
  refine bind_congr fun pksk => ?_
  -- Reduce the eufNma side `Prod.fst <$> _` to a bind, so both sides bind over
  -- `simulatedNmaAdv.main`, then compare the verification wrappers pointwise.
  change ((simulatedNmaAdv ids hr M maxAttempts sim adv).main pksk.1 >>= fun result =>
      withCacheOverlay result.2
        ((FiatShamirWithAbort ids hr M maxAttempts).verify
          pksk.1 result.1.1 result.1.2)) =
    (Prod.fst <$> (simulatedNmaAdv ids hr M maxAttempts sim adv).main pksk.1) >>= fun ms =>
      (FiatShamirWithAbort ids hr M maxAttempts).verify pksk.1 ms.1 ms.2
  rw [map_eq_bind_pure_comp, bind_assoc]
  -- Unfold `.main` to expose the inner managed run followed by the Option-B
  -- post-processing, then `bind_congr` over the inner run.
  simp only [simulatedNmaAdv, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun r => ?_
  -- `r.1.2` is the inner forgery's signature; the post-processed cache erases its own
  -- verification point, so the overlay verification agrees with the plain verification.
  refine withCacheOverlay_verify_eq_of_miss ids hr M maxAttempts _ pksk.1 r.1.1 r.1.2 ?_
  intro w' z hσ
  simp only [hσ, Function.update_self]

/-! ## Assembly -/

omit [SampleableType Stmt] in
/-- **CMA-to-NMA reduction for Fiat-Shamir with aborts** (after Theorem 3, CRYPTO 2023),
at the managed-RO NMA interface: for any EUF-CMA adversary making at most `qS` signing
and `qH` hash queries, the CMA advantage is bounded by the managed-RO NMA success
probability of `simulatedNmaAdv` plus the statistical loss `cmaToNmaLoss`.

The good-key event `Good` plays the role of the event `Γ` in the paper's Lemma 1: `δ`
bounds its complement under key generation, while `ε` and `p_abort` bound the per-key
commitment-guessing and per-attempt abort probabilities pointwise on it. -/
theorem euf_cma_to_nma
    (ζ_zk : ℝ) (hζ : 0 ≤ ζ_zk) (hhvzk : ids.HVZK sim ζ_zk)
    (qS qH : ℕ) (ε p_abort δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p_abort) (hp : p_abort < 1)
    (Good : Stmt → Wit → Prop)
    (hGood : Pr[ fun xw : Stmt × Wit => ¬ Good xw.1 xw.2 | hr.gen] ≤ ENNReal.ofReal δ)
    (hGuess : ∀ pk sk, Good pk sk → ∀ cm : Commit,
      Pr[= cm | Prod.fst <$> ids.commit pk sk] ≤ ENNReal.ofReal ε)
    (hAbort : ∀ pk sk, Good pk sk →
      Pr[= none | ids.honestExecution pk sk] ≤ ENNReal.ofReal p_abort)
    (hAbortSim : ∀ pk sk, Good pk sk →
      Pr[= none | sim pk] ≤ ENNReal.ofReal p_abort)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    adv.advantage (runtime M) ≤
      Pr[= true | SignatureAlg.managedRoNmaExp (runtime M)
        (simulatedNmaAdv ids hr M maxAttempts sim adv)] +
      ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  classical
  -- `advantage = Pr[G₀]` via the per-key bridge `G₀`.
  rw [SignatureAlg.unforgeableAdv.advantage,
    probOutput_unforgeableExp_eq_hybridExpAtKey_real ids hr M maxAttempts adv]
  -- Nonnegativity of the three per-hop slack pieces.
  have h1p : (0 : ℝ) < 1 - p_abort := by linarith
  have hA : 0 ≤ qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) + qS * (qH + 1) * ε / (1 - p_abort) :=
    add_nonneg
      (div_nonneg (by positivity) (by positivity))
      (div_nonneg (by positivity) (le_of_lt h1p))
  have hB : 0 ≤ qS * (qH + 1) * ε / (1 - p_abort) := div_nonneg (by positivity) (le_of_lt h1p)
  have hC : 0 ≤ qS * ζ_zk / (1 - p_abort) := div_nonneg (by positivity) (le_of_lt h1p)
  have hPK : 0 ≤ perKeyLoss qS qH ε p_abort ζ_zk := by unfold perKeyLoss; positivity
  -- Per-key chain on good keys: `real ≤ sim + ofReal (perKeyLoss)`.
  have hperkey : ∀ x ∈ support hr.gen, Good x.1 x.2 →
      Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
        Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
          (simSignBody M maxAttempts sim x.1 x.2) x.1] +
        ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) := by
    rintro ⟨pk, sk⟩ hmem hgood
    have hrel : rel pk sk = true := hr.gen_sound pk sk hmem
    have step1 := probOutput_hybridExpAtKey_real_le_prog ids hr M maxAttempts adv qS qH ε p_abort
      hp₀ hp hQ pk sk (hGuess pk sk hgood) (hAbort pk sk hgood)
    have step2 := probOutput_hybridExpAtKey_prog_le_trans ids hr M maxAttempts adv qS qH ε p_abort
      hp₀ hp hε hQ pk sk (hGuess pk sk hgood) (hAbort pk sk hgood)
    have step3 := probOutput_hybridExpAtKey_trans_le_sim ids hr M maxAttempts sim adv ζ_zk hζ hhvzk
      qS qH p_abort hp₀ hp hQ pk sk hrel (hAbortSim pk sk hgood)
    -- Chain the three hops and collapse the `ofReal` sums (slack pieces nonneg).
    calc Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts pk sk) pk]
        ≤ Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (fun x ↦ progSignBody ids M pk sk x maxAttempts) pk] +
            ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
              qS * (qH + 1) * ε / (1 - p_abort)) := step1
      _ ≤ (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (transSignBody ids M maxAttempts pk sk) pk] +
            ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort))) +
            ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
              qS * (qH + 1) * ε / (1 - p_abort)) := by gcongr
      _ ≤ ((Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim pk sk) pk] +
            ENNReal.ofReal (qS * ζ_zk / (1 - p_abort))) +
            ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort))) +
            ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
              qS * (qH + 1) * ε / (1 - p_abort)) := by gcongr
      _ = Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim pk sk) pk] +
            ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) := by
          have hcollapse :
              ENNReal.ofReal (qS * ζ_zk / (1 - p_abort)) +
                ENNReal.ofReal (qS * (qH + 1) * ε / (1 - p_abort)) +
                ENNReal.ofReal (qS * ε * (qS + 1) / (2 * (1 - p_abort) ^ 2) +
                  qS * (qH + 1) * ε / (1 - p_abort)) =
                ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) := by
            rw [← ENNReal.ofReal_add hC hB, ← ENNReal.ofReal_add (add_nonneg hC hB) hA]
            congr 1
            unfold perKeyLoss
            ring
          rw [add_assoc, add_assoc, ← add_assoc (ENNReal.ofReal (qS * ζ_zk / (1 - p_abort))),
            hcollapse]
  -- Average the per-key bound over `hr.gen`, paying `δ` on the complement of `Good`.
  have hbound : Pr[= true | do
        let x ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
      Pr[= true | do
        let x ← hr.gen
        hybridExpAtKey ids hr M maxAttempts adv (simSignBody M maxAttempts sim x.1 x.2) x.1] +
        ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) + ENNReal.ofReal δ := by
    simp only [probOutput_bind_eq_tsum]
    -- Pointwise: split on `Good`. On `Good` use `hperkey`; off `Good` charge the `δ` slot.
    have hpt : ∀ x : Stmt × Wit,
        Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
          Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (simSignBody M maxAttempts sim x.1 x.2) x.1] +
          Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) +
          Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0) := by
      intro x
      by_cases hx : x ∈ support hr.gen
      · by_cases hg : Good x.1 x.2
        · have := mul_le_mul' (le_refl (Pr[= x | hr.gen])) (hperkey x hx hg)
          calc Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                  (realSignBody ids M maxAttempts x.1 x.2) x.1]
              ≤ Pr[= x | hr.gen] *
                  (Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                    (simSignBody M maxAttempts sim x.1 x.2) x.1] +
                  ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk)) := this
            _ = Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                  (simSignBody M maxAttempts sim x.1 x.2) x.1] +
                Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) :=
                mul_add ..
            _ ≤ _ := by simp [hg]
        · -- Off `Good`: real ≤ 1, charged to the indicator slot.
          have : Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
                  (realSignBody ids M maxAttempts x.1 x.2) x.1] ≤
              Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0) := by
            simp only [hg, not_false_eq_true, if_true]
            exact mul_le_mul' le_rfl probOutput_le_one
          exact le_trans this le_add_self
      · simp [probOutput_eq_zero_of_not_mem_support hx]
    calc ∑' x, Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
            (realSignBody ids M maxAttempts x.1 x.2) x.1]
        ≤ ∑' x, (Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim x.1 x.2) x.1] +
            Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) +
            Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0)) :=
          ENNReal.tsum_le_tsum hpt
      _ = (∑' x, Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim x.1 x.2) x.1]) +
            (∑' x, Pr[= x | hr.gen] * ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk)) +
            (∑' x, Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0)) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add]
      _ ≤ (∑' x, Pr[= x | hr.gen] * Pr[= true | hybridExpAtKey ids hr M maxAttempts adv
              (simSignBody M maxAttempts sim x.1 x.2) x.1]) +
            ENNReal.ofReal (perKeyLoss qS qH ε p_abort ζ_zk) + ENNReal.ofReal δ := by
          gcongr
          · rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
          · calc ∑' x, Pr[= x | hr.gen] * (if ¬ Good x.1 x.2 then 1 else 0)
                = ∑' x, if ¬ Good x.1 x.2 then Pr[= x | hr.gen] else 0 := by
                  refine tsum_congr fun x => ?_; by_cases hg : Good x.1 x.2 <;> simp [hg]
              _ = Pr[fun xw : Stmt × Wit => ¬ Good xw.1 xw.2 | hr.gen] := by
                  rw [probEvent_eq_tsum_ite]
              _ ≤ ENNReal.ofReal δ := hGood
  -- Final: glue with the NMA bridge and reassociate the loss.
  refine le_trans hbound ?_
  rw [cmaToNmaLoss_eq_perKeyLoss_add, ENNReal.ofReal_add hPK hδ, add_assoc]
  gcongr
  exact probOutput_hybridExp_sim_le_managedRoNmaExp ids hr M maxAttempts sim adv

omit [SampleableType Stmt] [SampleableType Chal] in
/-- Cache-invariant companion to `simulatedNmaAdv`: the reduction issues at most `qH`
live hash queries (the signing simulation samples transcripts using only uniform
queries and programs the managed cache). Mirrors
`FiatShamir.simulatedNmaAdv_hashQueryBound` from the Σ-protocol track. -/
lemma simulatedNmaAdv_nmaHashQueryBound
    [Finite Chal] [Inhabited Chal]
    (qS qH : ℕ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    ∀ pk, FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulatedNmaAdv ids hr M maxAttempts sim adv).main pk) qH := by
  haveI : Fintype Chal := Fintype.ofFinite Chal
  letI : IsUniformSpec ((M × Commit →ₒ Chal) : OracleSpec _) :=
    IsUniformSpec.ofFintypeInhabited _
  intro pk
  let spec := unifSpec + (M × Commit →ₒ Chal)
  let fwd : QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget _
  let unifSim : QueryImpl unifSpec (StateT spec.QueryCache (OracleComp spec)) :=
    fun n => fwd (.inl n)
  let roSim : QueryImpl (M × Commit →ₒ Chal)
      (StateT spec.QueryCache (OracleComp spec)) := fun mc => do
    let cache ← get
    match cache (.inr mc) with
    | some v => pure v
    | none => do
        let v ← fwd (.inr mc)
        modifyGet fun cache => (v, cache.cacheQuery (.inr mc) v)
  let sigSim : QueryImpl (M →ₒ Option (Commit × Resp))
      (StateT spec.QueryCache (OracleComp spec)) := fun msg => do
    let r ← simulateQ unifSim (firstSome (sim pk) maxAttempts)
    match r with
    | some (w, c, z) =>
        modifyGet fun cache => (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
    | none => pure none
  -- Step bound for `fwd`: 0 live hash queries on `.inl`, exactly 1 on `.inr`.
  have hfwd :
      ∀ (t : spec.Domain) (s : spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (fwd t).run s) (match t with
            | .inl _ => 0
            | .inr _ => 1) := by
    intro t s
    cases t with
    | inl n =>
        simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
          OracleComp.liftM_run_StateT] using
          (FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
            (show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := liftM (spec.query (.inl n))) 0 by
                exact (FiatShamir.nmaHashQueryBound_query_iff (M := M) (Commit := Commit)
                  (Chal := Chal) (.inl n) 0).2 trivial)
            (fun u =>
              show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := pure (u, s)) 0 by
                  trivial))
    | inr mc =>
        simpa [fwd, QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply,
          OracleComp.liftM_run_StateT] using
          (FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit) (Chal := Chal)
            (show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
              (oa := liftM (spec.query (.inr mc))) 1 by
                exact (FiatShamir.nmaHashQueryBound_query_iff (M := M) (Commit := Commit)
                  (Chal := Chal) (.inr mc) 1).2 (Nat.succ_pos 0))
            (fun u =>
              show FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
                (oa := pure (u, s)) 0 by
                  trivial))
  -- Step bound for `roSim`: a cache hit issues no live query, a miss issues exactly one.
  have hro :
      ∀ (mc : M × Commit) (s : spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (roSim mc).run s) 1 := by
    intro mc s
    cases hs : s (.inr mc) with
    | some v =>
        simp [roSim, hs, FiatShamir.nmaHashQueryBound]
    | none =>
        simp only [FiatShamir.nmaHashQueryBound, Sum.forall, Prod.forall, StateT.run_bind,
          StateT.run_get, pure_bind, hs, StateT.run_modifyGet, bind_pure_comp,
          isQueryBoundP_map_iff, roSim] at ⊢ hfwd
        exact hfwd.2 mc.1 mc.2 s
  -- Step bound for `sigSim`: the simulator loop samples under `unifSim` (uniform-only)
  -- and then programs the managed cache, issuing no live hash query.
  have hsig :
      ∀ (msg : M) (s : spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (sigSim msg).run s) 0 := by
    intro msg s
    have htranscript :
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := (simulateQ unifSim (firstSome (sim pk) maxAttempts)).run s) 0 := by
      unfold FiatShamir.nmaHashQueryBound
      refine OracleComp.IsQueryBoundP.simulateQ_run_of_step
        (p := fun _ : ℕ => False) (impl := unifSim)
        (oa := firstSome (sim pk) maxAttempts)
        (OracleComp.isQueryBoundP_false _ _)
        (fun _ h _ => h.elim)
        ?_ s
      intro n _ s'
      have h := hfwd (.inl n) s'
      simpa [unifSim, FiatShamir.nmaHashQueryBound] using h
    have hcont : ∀ (rs : Option (Commit × Chal × Resp) × spec.QueryCache),
        FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
          (oa := StateT.run
            (match rs.1 with
              | some (w, c, z) => modifyGet fun cache =>
                  (some (w, z), cache.cacheQuery (.inr (msg, w)) c)
              | none =>
                  (pure none : StateT spec.QueryCache (OracleComp spec)
                    (Option (Commit × Resp)))) rs.2) 0 := by
      rintro ⟨(_ | ⟨w, c, z⟩), cache⟩ <;>
        simp [FiatShamir.nmaHashQueryBound, StateT.run_modifyGet]
    have hbind := FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit)
      (Chal := Chal) htranscript (fun rs => hcont rs)
    simpa [sigSim, StateT.run_bind] using hbind
  -- The run-level managed simulation issues at most `qH` live hash queries; the final
  -- pure post-processing (erasing the forgery's own verification point from the returned
  -- cache, Option B) issues none, so the total bound is `qH + 0 = qH`.
  have hrun : FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
      (oa := (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅) qH := by
    unfold FiatShamir.nmaHashQueryBound
    refine OracleComp.IsQueryBoundP.simulateQ_run_of_step (hQ pk).2 ?_ ?_ ∅
    · rintro ((n | mc) | msg) hp s'
      · simp at hp
      · simpa only [QueryImpl.add_apply_inl, QueryImpl.add_apply_inr] using hro mc s'
      · simp at hp
    · rintro ((n | mc) | msg) hnp s'
      · have h := hfwd (.inl n) s'
        simpa only [QueryImpl.add_apply_inl, FiatShamir.nmaHashQueryBound] using h
      · simp at hnp
      · simpa only [QueryImpl.add_apply_inr] using hsig msg s'
  have hpost : ∀ result : (M × Option (Commit × Resp)) × spec.QueryCache,
      FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
        (oa := (pure ((result.1.1, result.1.2),
          match result.1.2 with
          | some (w', _) => Function.update result.2 (Sum.inr (result.1.1, w')) none
          | none => result.2) :
          OracleComp spec ((M × Option (Commit × Resp)) × spec.QueryCache))) 0 := by
    intro result
    simp [FiatShamir.nmaHashQueryBound]
  have hbind := FiatShamir.nmaHashQueryBound_bind (M := M) (Commit := Commit)
    (Chal := Chal) hrun (fun result => hpost result)
  change FiatShamir.nmaHashQueryBound (M := M) (Commit := Commit) (Chal := Chal)
    (oa := (simulateQ ((unifSim + roSim) + sigSim) (adv.main pk)).run ∅ >>= fun result =>
      pure ((result.1.1, result.1.2),
        match result.1.2 with
        | some (w', _) => Function.update result.2 (Sum.inr (result.1.1, w')) none
        | none => result.2)) qH
  simpa only [Nat.add_zero] using hbind

end scaffold


end EUF_CMA

end FiatShamirWithAbort
