/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.Falcon.PrecisionSampling
public import LatticeCrypto.DiscreteGaussian.RenyiShift
public import VCVio.OracleComp.SimSemantics.Renyi

/-!
# Rényi precision transfer for Falcon signing with an ideal sampler

Two primitive bundles `prims` (the reference) and `primsB` (the perturbed one) share their hash,
public-key encoding and compression and may differ in the FFT fields. `idealExperiment prims A`
runs an experiment `A` with uniform coins and a signing oracle answered by `idealSign prims`:
VCVio's `sign` with every `samplerZ μ σ` call answered by the discrete Gaussian `D_{σ,μ}`.

`idealExperiment_precision` transfers success from the perturbed bundle to the reference one:
if `A` makes at most `K` signing queries, then for every measurable event `s` and every `T ≥ 1`,

`T · 2^{-(λ-1)} < Pr[idealExperiment primsB A ∈ s]`
`  → T · 2^{-λ} < Pr[idealExperiment prims A ∈ s] + K · maxAttempts · preimageTailMass prims sk Z`,

under these hypotheses:
* the two `ffSampling` targets `toFFTTarget` are within squared slotwise distance `E2`
  (`slotsSqDist`), for every hash target;
* every leaf of the tree is at least `σlo ≥ 1.277`, every slot of the root factor `ℓ` is at most
  `Lroot` and every slot of the other factors at most `Lin` (`FalconTree.FactorsLeRoot`), with
  growth constants `μroot`, `μin` (`L² ≤ (μ - 1)(μ - 1 - L²)`, `1 + L² ≤ μ`);
* the two bundles' `fromFFTPreimage` agree on every sampled pair whose coefficients are at most
  `Z` (`PreimageCoeffsLe`);
* `precisionRate λ σlo · K · maxAttempts · ffSamplingGrowth κ μroot μin · E2 ≤ log 2 / 2`,
  `κ = p.fftDepth`.

The proof couples the two signers (`jointSign`): one run computes both centres of every sampler
call. Answered at the perturbed centres it is the perturbed signer; answered at the reference
centres it is the hybrid signer `hybridSign`, which samples at the reference centres and
post-processes with `primsB`. A call whose centres differ by `δ` has
`R_{2λ-1} ≤ exp(precisionRate λ σlo · δ²)` (`renyiDiv_discreteGaussianMeasure_add_le`). Along
every execution the squared centre differences of one `ffSampling` run sum to at most
`ffSamplingGrowth κ μroot μin · E2` (`pathSum_ffSamplingJoint_root`), so the adaptive hybrid
along executions `OracleComp.renyiMGF_simulateQ_le_of_pathSum` bounds the Rényi divergence of
order `2λ - 1` of the two experiments by `√2`, and
`InformationTheory.lt_measure_of_renyiDiv_le_sqrt_two` transfers the event. The hybrid and the
reference signer differ only when a sampled pair has a coefficient above `Z`; per signing attempt
this has probability at most `preimageTailMass prims sk Z`, the largest such probability over hash
targets under the reference ideal signer, which gives the additive term.

## What is not proved

* The sampler is ideal on both sides: every `samplerZ` call is answered by `D_{σ,μ}`. Nothing is
  proved about `prims.samplerZ` (`Primitives.SamplerQuality` is not used); the concrete sampler is
  not covered.
* `preimageTailMass` stays an explicit additive term. `preimageTailMass_le` bounds it for any
  tree, and `preimageTailMass_falcon512_le` at Falcon-512 when the tree is the true tree of a key
  satisfying the NTRU equation (`trueTree`).
* The tree is a field of the secret key that nothing here ties to `f, g, F, G`: the leaf range and
  the factor bounds `Lroot`, `Lin` are hypotheses. The leaf of `ffSampling` samples both halves at
  one `σ` with no `ℓ` step at `n = 2`, unlike Falcon's `logn = 1` level. Both signers use the same
  tree, so the leaf standard deviations are equal on the two sides and only the centres differ.
* The key pair and the hash target are fixed inputs: key generation is not part of the experiment,
  and no running-time or cost model ties `T` to `A`. This is not an EUF-CMA bound; it transfers the
  probability of any event of an experiment that uses the signer as an oracle.
* The bounds hold along every execution: the summed squared centre differences are bounded by
  the targets' squared slotwise distance and the factor bounds, not averaged.
-/

public section

open OracleComp OracleSpec LatticeCrypto MeasureTheory InformationTheory
open scoped ENNReal

namespace Falcon

variable {p : Params}

/-! ## The experiment -/

/-- Signing queries of an experiment: a message, answered by an optional signature. -/
@[expose] def signOracleSpec : OracleSpec (List Byte) := List Byte →ₒ Option Signature

/-- The queries of an experiment that are signing queries. -/
@[expose] def IsSignQuery : ℕ ⊕ List Byte → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsSignQuery
  | .inl _ => isFalse fun h => h
  | .inr _ => isTrue trivial

variable (p) in
/-- The signing oracle of `idealExperiment`: uniform coins forwarded, messages signed by
`idealSign`. -/
@[expose] noncomputable def idealSignImpl (prims : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (maxAttempts : ℕ) :
    QueryImpl (unifSpec + signOracleSpec) (OracleComp (unifSpec + idealSamplerSpec)) :=
  unifLift idealSamplerSpec +
    (show QueryImpl signOracleSpec (OracleComp (unifSpec + idealSamplerSpec)) from
      fun msg => idealSign p prims pk sk msg maxAttempts)

variable (p) in
/-- An experiment with uniform coins and a signing oracle answered by `idealSign prims`. -/
@[expose] noncomputable def idealExperiment (prims : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (maxAttempts : ℕ) {α : Type} (A : OracleComp (unifSpec + signOracleSpec) α) :
    OracleComp (unifSpec + idealSamplerSpec) α :=
  simulateQ (idealSignImpl p prims pk sk maxAttempts) A

/-- The sampled pair `z` is the packed FFT of an integer pair with coefficients at most `Z`. -/
@[expose] def PreimageCoeffsLe (κ : ℕ) (Z : ℝ) (z : FFTPair κ) : Prop :=
  ∃ a b : Fin (2 * 2 ^ κ) → ℤ, (∀ i, |(a i : ℝ)| ≤ Z) ∧ (∀ i, |(b i : ℝ)| ≤ Z) ∧
    z.1 = RealFFTPoly.ofCoeffs κ (fun i => (a i : ℝ)) ∧
    z.2 = RealFFTPoly.ofCoeffs κ (fun i => (b i : ℝ))

variable (p) in
/-- The largest probability, over hash targets, that the reference ffSampling with the ideal
sampler returns a pair with a coefficient above `Z`. -/
@[expose] noncomputable def preimageTailMass (prims : Primitives p) (sk : SecretKey p) (Z : ℝ) :
    ℝ≥0∞ :=
  ⨆ c : Rq p.n, Pr{let z ← (ffSamplingWith idealSamplerQuery p.fftDepth
    (toFFTTarget p prims c sk) sk.tree)}[¬ PreimageCoeffsLe p.fftDepth Z z]

/-- The per-call Rényi rate at order `2λ - 1` for leaves at least `σlo ≥ 1.277`: a call whose
centres differ by `δ` has `R_{2λ-1} ≤ exp(precisionRate λ σlo · δ²)`. -/
@[expose] noncomputable def precisionRate (lam : ℕ) (σlo : ℝ) : ℝ :=
  (2 * lam - 1) / (2 * σlo ^ 2) + (2 * lam - 1) * (2 * lam) * (1 / 2 ^ 30) / (2 * (2 * lam - 2))

/-- The growth of the summed squared centre error through `κ` levels of ffSampling: `μroot / 2` at
the root and `μin / 2` at each of the `κ - 1` levels below. -/
@[expose] noncomputable def ffSamplingGrowth (κ : ℕ) (μroot μin : ℝ) : ℝ :=
  μroot / 2 * (μin / 2) ^ (κ - 1)

/-- The coupled run at depth `κ ≥ 1` charges at most `ffSamplingGrowth κ μroot μin` times the
squared slotwise distance of its targets. -/
theorem pathSum_ffSamplingJoint_growth {Lroot Lin μroot μin : ℝ}
    (hμroot : Lroot ^ 2 ≤ (μroot - 1) * (μroot - 1 - Lroot ^ 2))
    (hμroot' : 1 + Lroot ^ 2 ≤ μroot) (hμin : Lin ^ 2 ≤ (μin - 1) * (μin - 1 - Lin ^ 2))
    (hμin' : 1 + Lin ^ 2 ≤ μin) (κ : ℕ) (hκ : 1 ≤ κ) (t u : FFTPair κ) (tree : FalconTree κ)
    (htree : tree.FactorsLeRoot Lroot Lin) :
    PathSum jointWeight (ffSamplingJoint κ t u tree)
      (ffSamplingGrowth κ μroot μin * (slotsSqDist u.1 t.1 + slotsSqDist u.2 t.2)) := by
  cases κ with
  | zero => omega
  | succ κ =>
    rw [ffSamplingGrowth, Nat.add_sub_cancel]
    exact pathSum_ffSamplingJoint_root hμroot hμroot' hμin hμin' κ t u tree htree

/-! ## Queries -/

/-- `unifLift` forwards a coin query to the left summand. -/
theorem unifLift_eq {ι : Type} (spec : OracleSpec.{0, 0} ι) (n : ℕ) :
    unifLift spec n = liftM ((unifSpec + spec).query (Sum.inl n)) := by
  rw [unifLift, QueryImpl.ofLift_apply, OracleComp.liftM_eq_liftM_liftM,
    OracleQuery.liftM_add_left_query]

/-- An ideal sampler query denotes `idealSamplerMeasure`. -/
theorem evalDist_idealSamplerQuery (μ σ : ℝ) :
    @evalDist _ _ ℤ ⊤ (idealSamplerQuery μ σ) = idealSamplerMeasure μ σ :=
  (@evalDist_liftM_query _ (unifSpec + idealSamplerSpec) _ (Sum.inr (μ, σ)) ⊤).trans
    (@MeasureTheory.trim_eq_self _ ⊤ _)

/-! ## Bounds through `signWith` -/

section SignWith

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- `attemptWith` does not depend on the bundle. -/
theorem attemptWith_congr {m : Type → Type*} [Monad m] (prims prims' : Primitives p)
    (trap : Rq p.n → m (Rq p.n × Rq p.n)) :
    attemptWith p prims' trap = attemptWith p prims trap := rfl

/-- `signWith` uses a bundle only through its hash, public-key encoding and compression. -/
theorem signWith_congr {m : Type → Type*} [Monad m] (prims prims' : Primitives p)
    (hhash : prims'.hashToPoint = prims.hashToPoint)
    (hpkb : prims'.publicKeyBytes = prims.publicKeyBytes)
    (hcomp : prims'.compress = prims.compress) (salt : m (Bytes 40))
    (trap : Rq p.n → m (Rq p.n × Rq p.n)) (pk : PublicKey p) (msg : List Byte) :
    ∀ n, signWith p prims' salt trap pk msg n = signWith p prims salt trap pk msg n
  | 0 => rfl
  | n + 1 => by
    simp only [signWith, Primitives.hashToPointForPublicKey, hhash, hpkb, hcomp,
      attemptWith_congr prims prims', signWith_congr prims prims' hhash hpkb hcomp salt trap pk
        msg n]

/-- Every query of `signWith` satisfies `P` when every query of the salt draw and of every
trapdoor step does. -/
theorem allQueriesSatisfy_signWith (prims : Primitives p) {P : ι → Prop}
    {salt : OracleComp spec (Bytes 40)} {trap : Rq p.n → OracleComp spec (Rq p.n × Rq p.n)}
    (hsalt : AllQueriesSatisfy salt P) (htrap : ∀ c, AllQueriesSatisfy (trap c) P)
    (pk : PublicKey p) (msg : List Byte) :
    ∀ n, AllQueriesSatisfy (signWith p prims salt trap pk msg n) P
  | 0 => allQueriesSatisfy_pure _ _
  | n + 1 => by
    have ih := allQueriesSatisfy_signWith prims hsalt htrap pk msg n
    refine allQueriesSatisfy_bind hsalt fun s => allQueriesSatisfy_bind
      (allQueriesSatisfy_bind (htrap _) fun x => ?_) fun r => ?_
    · split_ifs <;> exact allQueriesSatisfy_pure _ _
    · rcases r with _ | ⟨_, s₂⟩
      · exact ih
      · dsimp only
        split
        · exact allQueriesSatisfy_pure _ _
        · exact ih

/-- A signing loop whose salt draw makes no charged query and whose trapdoor steps make at most
`c₀` makes at most `maxAttempts · c₀`. -/
theorem isQueryBoundP_signWith (prims : Primitives p) {S : ι → Prop} [DecidablePred S]
    {salt : OracleComp spec (Bytes 40)} {trap : Rq p.n → OracleComp spec (Rq p.n × Rq p.n)}
    {c₀ : ℕ} (hsalt : IsQueryBoundP salt S 0) (htrap : ∀ c, IsQueryBoundP (trap c) S c₀)
    (pk : PublicKey p) (msg : List Byte) :
    ∀ n, IsQueryBoundP (signWith p prims salt trap pk msg n) S (n * c₀)
  | 0 => isQueryBoundP_pure S _ _
  | n + 1 => by
    have ih := isQueryBoundP_signWith prims hsalt htrap pk msg n
    have hatt : ∀ c, IsQueryBoundP (attemptWith p prims trap c) S c₀ := fun c => by
      have h := isQueryBoundP_bind (htrap c) fun x _ =>
        (show IsQueryBoundP (if (falconPSF p prims).isShort x then
          (pure (some x) : OracleComp spec _) else pure none) S 0 by
            split_ifs <;> exact isQueryBoundP_pure S _ _)
      simpa [attemptWith] using h
    rw [signWith]
    refine (isQueryBoundP_bind hsalt fun s _ =>
      isQueryBoundP_bind (m := n * c₀) (hatt _) fun r _ => ?_).mono ?_
    · rcases r with _ | ⟨_, s₂⟩
      · exact ih
      · dsimp only
        split
        · exact isQueryBoundP_pure S _ _
        · exact ih
    · rw [Nat.succ_mul]; omega

/-- A signing loop whose salt draw has path sum `0` and whose trapdoor steps have path sum at
most `s₁ ≥ 0` has path sum at most `maxAttempts · s₁`. -/
theorem pathSum_signWith (prims : Primitives p) {w : ι → ℝ} {salt : OracleComp spec (Bytes 40)}
    {trap : Rq p.n → OracleComp spec (Rq p.n × Rq p.n)} {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (hsalt : PathSum w salt 0) (htrap : ∀ c, PathSum w (trap c) s₁) (pk : PublicKey p)
    (msg : List Byte) : ∀ n : ℕ, PathSum w (signWith p prims salt trap pk msg n) (n * s₁)
  | 0 => .pure _ (by simp)
  | n + 1 => by
    have ih := pathSum_signWith prims hs₁ hsalt htrap pk msg n
    have hatt : ∀ c, PathSum w (attemptWith p prims trap c) (s₁ + 0) := fun c => by
      unfold attemptWith
      exact (htrap c).bind fun x => by split <;> exact .pure _ le_rfl
    rw [signWith]
    refine (hsalt.bind (S₂ := s₁ + 0 + n * s₁) fun s =>
      (hatt _).bind (S₂ := n * s₁) fun r => ?_).weaken (le_of_eq ?_)
    · rcases r with _ | ⟨_, s₂⟩
      · exact ih
      · dsimp only
        split
        · exact .pure _ (mul_nonneg (Nat.cast_nonneg _) hs₁)
        · exact ih
    · push_cast; ring

variable [OracleSpec.AnswerMeasure spec]

/-- Signing loops whose trapdoor steps are within `ε` in total variation are within
`maxAttempts · ε`. -/
theorem measureETVDist_signWith_le (prims : Primitives p) (salt : OracleComp spec (Bytes 40))
    (trap₁ trap₂ : Rq p.n → OracleComp spec (Rq p.n × Rq p.n)) {ε : ℝ≥0∞}
    (h : ∀ c, letI : MeasurableSpace (Rq p.n × Rq p.n) := ⊤
      measureETVDist (trap₁ c) (trap₂ c) ≤ ε) (pk : PublicKey p) (msg : List Byte) :
    ∀ n, letI : MeasurableSpace (Option Signature) := ⊤
      measureETVDist (signWith p prims salt trap₁ pk msg n) (signWith p prims salt trap₂ pk msg n)
        ≤ n * ε
  | 0 => by simp [signWith, measureETVDist_self]
  | n + 1 => by
    let : MeasurableSpace (Option Signature) := ⊤
    let : MeasurableSpace (Bytes 40) := ⊤
    let : MeasurableSpace (Rq p.n × Rq p.n) := ⊤
    let : MeasurableSpace (Option (Rq p.n × Rq p.n)) := ⊤
    have : DiscreteMeasurableSpace (Bytes 40) := ⟨fun _ => trivial⟩
    have : DiscreteMeasurableSpace (Rq p.n × Rq p.n) := ⟨fun _ => trivial⟩
    have : DiscreteMeasurableSpace (Option (Rq p.n × Rq p.n)) := ⟨fun _ => trivial⟩
    have ih := measureETVDist_signWith_le prims salt trap₁ trap₂ h pk msg n
    have hstep : ∀ s : Bytes 40,
        measureETVDist
          (attemptWith p prims trap₁ (prims.hashToPointForPublicKey pk.h s msg) >>= fun r =>
            match r with
            | some (_, s₂) =>
                match prims.compress (rqToIntPolyCentered s₂) p.sbytelen with
                | some comp => return (some ⟨s, comp⟩)
                | none => signWith p prims salt trap₁ pk msg n
            | none => signWith p prims salt trap₁ pk msg n)
          (attemptWith p prims trap₂ (prims.hashToPointForPublicKey pk.h s msg) >>= fun r =>
            match r with
            | some (_, s₂) =>
                match prims.compress (rqToIntPolyCentered s₂) p.sbytelen with
                | some comp => return (some ⟨s, comp⟩)
                | none => signWith p prims salt trap₂ pk msg n
            | none => signWith p prims salt trap₂ pk msg n) ≤ ε + n * ε := by
      intro s
      refine (measureETVDist_bind_bind_le_add_lintegral _ _ _ _ Measurable.of_discrete
        Measurable.of_discrete (fun _ => (n : ℝ≥0∞) * ε)
        (Filter.Eventually.of_forall fun r => ?_)).trans ?_
      · rcases r with _ | ⟨_, s₂⟩
        · exact ih
        · dsimp only
          split
          · simp [measureETVDist_self]
          · exact ih
      · rw [lintegral_const]
        refine add_le_add ?_ (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _))
        exact (measureETVDist_bind_le _ _ _ Measurable.of_discrete).trans (h _)
    change measureETVDist (salt >>= _) (salt >>= _) ≤ _
    refine (measureETVDist_bind_bind_le_lintegral _ _ _ Measurable.of_discrete
      Measurable.of_discrete (fun _ => ε + n * ε)
      (Filter.Eventually.of_forall hstep)).trans ?_
    rw [lintegral_const]
    calc (ε + n * ε) * 𝒟[salt] Set.univ ≤ ε + n * ε :=
          mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring

end SignWith

/-! ## The coupled and hybrid signers -/

variable (p) in
/-- **The coupled signer.** One run of `sign` that computes, for every sampler call, the centre
from the reference target and the centre from the perturbed target, uses one answer for both, and
assembles the signature with `primsB`. -/
@[expose] noncomputable def jointSign (prims primsB : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (msg : List Byte) (maxAttempts : ℕ) :
    OracleComp (unifSpec + jointSamplerSpec) (Option Signature) :=
  signWith p primsB (liftComp ($ᵗ (Bytes 40)) (unifSpec + jointSamplerSpec))
    (fun c => do
      let z ← ffSamplingJoint p.fftDepth (toFFTTarget p prims c sk) (toFFTTarget p primsB c sk)
        sk.tree
      return fromFFTPreimage p primsB c sk z) pk msg maxAttempts

variable (p) in
/-- The hybrid signer: sampling at the reference centres, assembly with `primsB`. -/
@[expose] noncomputable def hybridSign (prims primsB : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (msg : List Byte) (maxAttempts : ℕ) :
    OracleComp (unifSpec + idealSamplerSpec) (Option Signature) :=
  signWith p primsB (liftComp ($ᵗ (Bytes 40)) (unifSpec + idealSamplerSpec))
    (fun c => do
      let z ← ffSamplingWith idealSamplerQuery p.fftDepth (toFFTTarget p prims c sk) sk.tree
      return fromFFTPreimage p primsB c sk z) pk msg maxAttempts

variable (p) in
/-- The signing oracle answered by `jointSign`. -/
@[expose] noncomputable def jointSignImpl (prims primsB : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (maxAttempts : ℕ) :
    QueryImpl (unifSpec + signOracleSpec) (OracleComp (unifSpec + jointSamplerSpec)) :=
  unifLift jointSamplerSpec +
    (show QueryImpl signOracleSpec (OracleComp (unifSpec + jointSamplerSpec)) from
      fun msg => jointSign p prims primsB pk sk msg maxAttempts)

variable (p) in
/-- The signing oracle answered by `hybridSign`. -/
@[expose] noncomputable def hybridSignImpl (prims primsB : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (maxAttempts : ℕ) :
    QueryImpl (unifSpec + signOracleSpec) (OracleComp (unifSpec + idealSamplerSpec)) :=
  unifLift idealSamplerSpec +
    (show QueryImpl signOracleSpec (OracleComp (unifSpec + idealSamplerSpec)) from
      fun msg => hybridSign p prims primsB pk sk msg maxAttempts)

/-- Answered at the perturbed centres, the coupled signer is `idealSign primsB`. -/
theorem simulateQ_jointSign_bar (prims primsB : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (msg : List Byte) (maxAttempts : ℕ) :
    simulateQ (jointAnswer JointQuery.centerBar) (jointSign p prims primsB pk sk msg maxAttempts) =
      idealSign p primsB pk sk msg maxAttempts := by
  have hsalt : simulateQ (jointAnswer JointQuery.centerBar)
      (liftComp ($ᵗ (Bytes 40)) (unifSpec + jointSamplerSpec)) =
        liftComp ($ᵗ (Bytes 40)) (unifSpec + idealSamplerSpec) :=
    QueryImpl.simulateQ_add_liftComp_left _ _ _
  rw [jointSign, idealSign, simulateQ_signWith, hsalt]
  congr 1
  funext c
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_ffSamplingJoint_bar]
  rfl

/-- Answered at the reference centres, the coupled signer is `hybridSign`. -/
theorem simulateQ_jointSign_center (prims primsB : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (msg : List Byte) (maxAttempts : ℕ) :
    simulateQ (jointAnswer JointQuery.center) (jointSign p prims primsB pk sk msg maxAttempts) =
      hybridSign p prims primsB pk sk msg maxAttempts := by
  have hsalt : simulateQ (jointAnswer JointQuery.center)
      (liftComp ($ᵗ (Bytes 40)) (unifSpec + jointSamplerSpec)) =
        liftComp ($ᵗ (Bytes 40)) (unifSpec + idealSamplerSpec) :=
    QueryImpl.simulateQ_add_liftComp_left _ _ _
  rw [jointSign, hybridSign, simulateQ_signWith, hsalt]
  congr 1
  funext c
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_ffSamplingJoint_center]

/-- Answered at the perturbed centres, the coupled experiment is the perturbed experiment. -/
theorem simulateQ_jointExperiment_bar (prims primsB : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (maxAttempts : ℕ) {α : Type}
    (A : OracleComp (unifSpec + signOracleSpec) α) :
    simulateQ (jointAnswer JointQuery.centerBar)
        (simulateQ (jointSignImpl p prims primsB pk sk maxAttempts) A) =
      idealExperiment p primsB pk sk maxAttempts A := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) A
  rcases t with n | msg
  · exact QueryImpl.simulateQ_add_liftM_query_left _ _ n
  · exact simulateQ_jointSign_bar prims primsB pk sk msg maxAttempts

/-- Answered at the reference centres, the coupled experiment is the hybrid experiment. -/
theorem simulateQ_jointExperiment_center (prims primsB : Primitives p) (pk : PublicKey p)
    (sk : SecretKey p) (maxAttempts : ℕ) {α : Type}
    (A : OracleComp (unifSpec + signOracleSpec) α) :
    simulateQ (jointAnswer JointQuery.center)
        (simulateQ (jointSignImpl p prims primsB pk sk maxAttempts) A) =
      simulateQ (hybridSignImpl p prims primsB pk sk maxAttempts) A := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) A
  rcases t with n | msg
  · exact QueryImpl.simulateQ_add_liftM_query_left _ _ n
  · exact simulateQ_jointSign_center prims primsB pk sk msg maxAttempts

/-! ## The Rényi step -/

/-- **One coupled call.** A call whose leaf is at least `σlo ≥ 1.277` has Rényi MGF of order
`a = 2λ - 1` between its answers at the perturbed and at the reference centres at most
`exp((a - 1) · precisionRate λ σlo · jointWeight t)`: Lemma 4 of ePrint 2026/1531 with the
explicit curvature term at a shift `δ`, `jointWeight t = δ²`. A coin query has weight `0`. -/
theorem renyiMGF_jointAnswer_le (σlo : ℝ) (hσlo : 1277 / 1000 ≤ σlo) (lam : ℕ) (hlam : 2 ≤ lam)
    (t : ℕ ⊕ JointQuery) (hV : JointLeafGe σlo t) :
    @renyiMGF _ ⊤ (2 * (lam : ℝ) - 1) (@evalDist _ _ _ ⊤ (jointAnswer JointQuery.centerBar t))
      (@evalDist _ _ _ ⊤ (jointAnswer JointQuery.center t)) ≤
        ENNReal.ofReal (Real.exp ((2 * (lam : ℝ) - 1 - 1) * precisionRate lam σlo *
          jointWeight t)) := by
  set a : ℝ := 2 * lam - 1 with ha_def
  set c := (a - 1) * precisionRate lam σlo with hc_def
  have hlam' : (2 : ℝ) ≤ lam := by exact_mod_cast hlam
  have ha : 1 < a := by rw [ha_def]; linarith
  have hσlo0 : 0 < σlo := lt_of_lt_of_le (by norm_num) hσlo
  rcases t with n | q
  · let : MeasurableSpace (Fin (n + 1)) := ⊤
    have : MeasurableSingletonClass (Fin (n + 1)) := ⟨fun _ => trivial⟩
    change renyiMGF a 𝒟[unifLift idealSamplerSpec n] 𝒟[unifLift idealSamplerSpec n] ≤
      ENNReal.ofReal (Real.exp (c * 0))
    rw [mul_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact renyiMGF_self_le ha _ (evalDist_apply_univ_le_one (unifLift idealSamplerSpec n))
  have hσ : σlo ≤ q.sigma := hV
  have hσ0 : 0 < q.sigma := lt_of_lt_of_le hσlo0 hσ
  change @renyiMGF ℤ ⊤ a (@evalDist _ _ ℤ ⊤ (idealSamplerQuery q.centerBar q.sigma))
    (@evalDist _ _ ℤ ⊤ (idealSamplerQuery q.center q.sigma)) ≤
      ENNReal.ofReal (Real.exp (c * (q.centerBar - q.center) ^ 2))
  rw [evalDist_idealSamplerQuery, evalDist_idealSamplerQuery, idealSamplerMeasure_of_pos hσ0,
    idealSamplerMeasure_of_pos hσ0]
  obtain ⟨hT, hcurv⟩ := Theta.tail_lt_one_and_curvature_le q.sigma (hσlo.trans hσ)
  have h4 := renyiDiv_discreteGaussianMeasure_add_le q.sigma q.center
    (q.centerBar - q.center) a hσ0 ha hT
  rw [add_sub_cancel] at h4
  refine (renyiMGF_le_of_renyiDiv_le ha h4).trans (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.2 ?_))
  set δ := q.centerBar - q.center
  have hσ2 : σlo ^ 2 ≤ q.sigma ^ 2 := pow_le_pow_left₀ hσlo0.le hσ 2
  have ha0 : 0 < a - 1 := by linarith
  have e1 : a * δ ^ 2 / (2 * q.sigma ^ 2) ≤ a * δ ^ 2 / (2 * σlo ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have e2 : a * (a + 1) * δ ^ 2 * Theta.curvature q.sigma / (2 * (a - 1)) ≤
      a * (a + 1) * δ ^ 2 * (1 / 2 ^ 30) / (2 * (a - 1)) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    have haa : 0 ≤ a * (a + 1) * δ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hcurv haa
  have hP : c * δ ^ 2 = (a - 1) * (a * δ ^ 2 / (2 * σlo ^ 2) +
      a * (a + 1) * δ ^ 2 * (1 / 2 ^ 30) / (2 * (a - 1))) := by
    rw [hc_def, precisionRate, ha_def]; ring
  rw [hP]
  exact mul_le_mul_of_nonneg_left (by linarith) ha0.le

/-- **The Rényi step.** If the two `ffSampling` targets are within squared slotwise distance `E2`
for every hash target, the tree has leaves at least `σlo ≥ 1.277`, root factor slots at most
`Lroot` and the other factor slots at most `Lin`, and `A` makes at most `K` signing queries, the
perturbed and hybrid experiments are within
`R_{2λ-1} ≤ exp(precisionRate λ σlo · K · maxAttempts · ffSamplingGrowth κ μroot μin · E2)`. -/
theorem renyiDiv_jointExperiment_le (prims primsB : Primitives p) (hdepth : 1 ≤ p.fftDepth)
    (pk : PublicKey p) (sk : SecretKey p) (E2 : ℝ)
    (htarget : ∀ c, slotsSqDist (toFFTTarget p primsB c sk).1 (toFFTTarget p prims c sk).1 +
      slotsSqDist (toFFTTarget p primsB c sk).2 (toFFTTarget p prims c sk).2 ≤ E2)
    (σlo σhi : ℝ) (hσlo : 1277 / 1000 ≤ σlo) (hleaves : sk.tree.LeavesIn σlo σhi)
    (Lroot Lin μroot μin : ℝ) (hμroot : Lroot ^ 2 ≤ (μroot - 1) * (μroot - 1 - Lroot ^ 2))
    (hμroot' : 1 + Lroot ^ 2 ≤ μroot) (hμin : Lin ^ 2 ≤ (μin - 1) * (μin - 1 - Lin ^ 2))
    (hμin' : 1 + Lin ^ 2 ≤ μin) (hfactors : sk.tree.FactorsLeRoot Lroot Lin)
    (lam : ℕ) (hlam : 2 ≤ lam) (maxAttempts K : ℕ)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (A : OracleComp (unifSpec + signOracleSpec) α) (hK : IsQueryBoundP A IsSignQuery K) :
    renyiDiv (2 * lam - 1)
        𝒟[simulateQ (jointAnswer JointQuery.centerBar)
          (simulateQ (jointSignImpl p prims primsB pk sk maxAttempts) A)]
        𝒟[simulateQ (jointAnswer JointQuery.center)
          (simulateQ (jointSignImpl p prims primsB pk sk maxAttempts) A)] ≤
      ENNReal.ofReal (Real.exp (precisionRate lam σlo *
        (K * maxAttempts * (ffSamplingGrowth p.fftDepth μroot μin * E2)))) := by
  set a : ℝ := 2 * lam - 1 with ha_def
  set G := ffSamplingGrowth p.fftDepth μroot μin with hG_def
  have hlam' : (2 : ℝ) ≤ lam := by exact_mod_cast hlam
  have ha : 1 < a := by rw [ha_def]; linarith
  have hrate : 0 ≤ precisionRate lam σlo := by
    have h1 : (0 : ℝ) ≤ 2 * lam - 1 := by linarith
    exact add_nonneg (div_nonneg h1 (by positivity))
      (div_nonneg (mul_nonneg (mul_nonneg h1 (by positivity)) (by norm_num)) (by linarith))
  set c := (a - 1) * precisionRate lam σlo with hc_def
  have hc : 0 ≤ c := mul_nonneg (by linarith) hrate
  have hsq0 : ∀ {k : ℕ} (f g : RealFFTPoly k), 0 ≤ slotsSqDist f g :=
    fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE2 : 0 ≤ E2 := (add_nonneg (hsq0 _ _) (hsq0 _ _)).trans (htarget 0)
  have hG : 0 ≤ G := by
    have : 0 ≤ μroot := by nlinarith
    have : 0 ≤ μin := by nlinarith
    rw [hG_def, ffSamplingGrowth]
    positivity
  have hB : ∀ t, JointLeafGe σlo t →
      @renyiMGF _ ⊤ a (@evalDist _ _ _ ⊤ (jointAnswer JointQuery.centerBar t))
        (@evalDist _ _ _ ⊤ (jointAnswer JointQuery.center t)) ≤
          ENNReal.ofReal (Real.exp (c * jointWeight t)) :=
    fun t hV => renyiMGF_jointAnswer_le σlo hσlo lam hlam t hV
  have hunifW : ∀ n, AllQueriesSatisfy (unifLift jointSamplerSpec n)
      fun t => jointWeight t = 0 :=
    fun n => by rw [unifLift_eq]; exact (allQueriesSatisfy_query_iff _ _).2 rfl
  have hunifV : ∀ n, AllQueriesSatisfy (unifLift jointSamplerSpec n) (JointLeafGe σlo) :=
    fun n => by rw [unifLift_eq]; exact (allQueriesSatisfy_query_iff _ _).2 trivial
  have hsaltV : AllQueriesSatisfy (liftComp ($ᵗ (Bytes 40)) (unifSpec + jointSamplerSpec))
      (JointLeafGe σlo) :=
    AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (fun _ => trivial) _)
      fun n _ => hunifV n
  have hsalt0 : PathSum jointWeight (liftComp ($ᵗ (Bytes 40)) (unifSpec + jointSamplerSpec)) 0 :=
    pathSum_zero_of_allQueriesSatisfy (AllQueriesSatisfy.simulateQ
      (allQueriesSatisfy_of_forall (fun _ => trivial) _) fun n _ => hunifW n)
  have hV : AllQueriesSatisfy (simulateQ (jointSignImpl p prims primsB pk sk maxAttempts) A)
      (JointLeafGe σlo) := by
    refine AllQueriesSatisfy.simulateQ (allQueriesSatisfy_of_forall (fun _ => trivial) A)
      fun t _ => ?_
    rcases t with n | msg
    · exact hunifV n
    · exact allQueriesSatisfy_signWith primsB hsaltV (fun c => allQueriesSatisfy_bind
        (allQueriesSatisfy_ffSamplingJoint_leafGe _ _ _ _ hleaves) fun _ =>
          allQueriesSatisfy_pure _ _) pk msg maxAttempts
  have hpath : PathSum jointWeight (simulateQ (jointSignImpl p prims primsB pk sk maxAttempts) A)
      (K * (maxAttempts * (G * E2))) := by
    refine PathSum.simulateQ_of_step (by positivity) hK (fun t ht => ?_) (fun t ht => ?_)
    · rcases t with n | msg
      · exact ht.elim
      · refine pathSum_signWith primsB (by positivity) hsalt0 (fun c => ?_) pk msg maxAttempts
        refine ((pathSum_ffSamplingJoint_growth hμroot hμroot' hμin hμin' _ hdepth _ _
          _ hfactors).bind fun _ => PathSum.pure _ le_rfl).weaken ?_
        rw [add_zero]
        exact mul_le_mul_of_nonneg_left (htarget c) hG
    · rcases t with n | msg
      · exact pathSum_zero_of_allQueriesSatisfy (hunifW n)
      · exact (ht trivial).elim
  have hM := renyiMGF_simulateQ_le_of_pathSum ha (jointAnswer JointQuery.centerBar)
    (jointAnswer JointQuery.center) (JointLeafGe σlo) jointWeight hc hB _ hV hpath
  have ham : a - 1 ≠ 0 := by linarith
  rw [renyiDiv_eq_rpow ha]
  calc _ ≤ ENNReal.ofReal (Real.exp (c * (K * (maxAttempts * (G * E2))))) ^ (a - 1)⁻¹ :=
        ENNReal.rpow_le_rpow hM (inv_nonneg.2 (by linarith))
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_nonneg.2 (by linarith)),
          ← Real.exp_mul, hc_def]
        congr 2
        field_simp

/-! ## The total-variation step -/

/-- **The total-variation step.** If the two bundles share hash, public-key encoding and
compression and their `fromFFTPreimage` agree on pairs with coefficients at most `Z`, the hybrid
experiment is within `K · maxAttempts · preimageTailMass prims sk Z` of the reference
experiment. -/
theorem evalDist_hybridExperiment_le (prims primsB : Primitives p)
    (hhash : primsB.hashToPoint = prims.hashToPoint)
    (hpkb : primsB.publicKeyBytes = prims.publicKeyBytes)
    (hcomp : primsB.compress = prims.compress) (pk : PublicKey p) (sk : SecretKey p) (Z : ℝ)
    (hpost : ∀ c z, PreimageCoeffsLe p.fftDepth Z z →
      fromFFTPreimage p primsB c sk z = fromFFTPreimage p prims c sk z)
    (maxAttempts K : ℕ) {α : Type} [MeasurableSpace α]
    (A : OracleComp (unifSpec + signOracleSpec) α) (hK : IsQueryBoundP A IsSignQuery K)
    {s : Set α} (hs : MeasurableSet s) :
    𝒟[simulateQ (hybridSignImpl p prims primsB pk sk maxAttempts) A] s ≤
      𝒟[idealExperiment p prims pk sk maxAttempts A] s +
        K * maxAttempts * preimageTailMass p prims sk Z := by
  let : MeasurableSpace (Rq p.n × Rq p.n) := ⊤
  have : DiscreteMeasurableSpace (Rq p.n × Rq p.n) := ⟨fun _ => trivial⟩
  let : MeasurableSpace (FFTPair p.fftDepth) := ⊤
  have : DiscreteMeasurableSpace (FFTPair p.fftDepth) := ⟨fun _ => trivial⟩
  have htrap : ∀ c : Rq p.n,
      measureETVDist (do
          let z ← ffSamplingWith idealSamplerQuery p.fftDepth (toFFTTarget p prims c sk) sk.tree
          return fromFFTPreimage p primsB c sk z)
        (trapdoorWith p prims sk idealSamplerQuery c) ≤ preimageTailMass p prims sk Z := by
    intro c
    rw [trapdoorWith, bind_pure_comp, bind_pure_comp]
    refine (measureETVDist_map_le_map_add_prEvent_bad _ _ id _ _
      (fun z => ¬ PreimageCoeffsLe p.fftDepth Z z)
      (fun z z' hz hbad => by subst hz; exact hpost c z (not_not.1 hbad))).trans ?_
    rw [id_map, measureETVDist_self, zero_add]
    exact le_iSup (fun c : Rq p.n => Pr{let z ← (ffSamplingWith idealSamplerQuery p.fftDepth
      (toFFTTarget p prims c sk) sk.tree)}[¬ PreimageCoeffsLe p.fftDepth Z z]) c
  have hTV := OracleComp.measureETVDist_simulateQ_le_queryBoundP_mul
    (hybridSignImpl p prims primsB pk sk maxAttempts) (idealSignImpl p prims pk sk maxAttempts)
    IsSignQuery (ε := maxAttempts * preimageTailMass p prims sk Z) (fun t ht => ?_)
    (fun t ht => ?_) A hK
  · have habs := (ENNReal.absDiff_le_iff.1 (measure_absDiff_apply_le_measureETVDist
      (simulateQ (hybridSignImpl p prims primsB pk sk maxAttempts) A)
      (idealExperiment p prims pk sk maxAttempts A) hs)).1
    calc _ ≤ _ := habs
      _ ≤ 𝒟[idealExperiment p prims pk sk maxAttempts A] s +
          K * (maxAttempts * preimageTailMass p prims sk Z) := add_le_add le_rfl hTV
      _ = _ := by rw [mul_assoc]
  · rcases t with n | msg
    · exact ht.elim
    · let : MeasurableSpace (Option Signature) := ⊤
      change measureETVDist (hybridSign p prims primsB pk sk msg maxAttempts)
        (idealSign p prims pk sk msg maxAttempts) ≤ _
      rw [hybridSign, signWith_congr prims primsB hhash hpkb hcomp, idealSign]
      exact measureETVDist_signWith_le prims _ _ _ htrap pk msg maxAttempts
  · rcases t with n | msg
    · exact (QueryImpl.add_apply_inl _ _ n).trans (QueryImpl.add_apply_inl _ _ n).symm
    · exact (ht trivial).elim

/-! ## The transfer -/

/-- **Rényi precision transfer for Falcon signing with an ideal sampler.** Two bundles that share
hash, public-key encoding and compression, whose `ffSampling` targets are within squared slotwise
distance `E2`, and whose `fromFFTPreimage` agree on sampled pairs with coefficients at most `Z`; a
tree with leaves at least `σlo ≥ 1.277`, root factor slots at most `Lroot` and the other factor
slots at most `Lin`, with growth constants `μroot`, `μin`; an experiment making at most `K`
signing queries; the budget
`precisionRate λ σlo · K · maxAttempts · ffSamplingGrowth κ μroot μin · E2 ≤ log 2 / 2`. Then an
event of probability above `T · 2^{-(λ-1)}` in the perturbed ideal experiment has probability
above `T · 2^{-λ}` in the reference one, up to `K · maxAttempts · preimageTailMass prims sk Z`. -/
theorem idealExperiment_precision (prims primsB : Primitives p) (hdepth : 1 ≤ p.fftDepth)
    (hhash : primsB.hashToPoint = prims.hashToPoint)
    (hpkb : primsB.publicKeyBytes = prims.publicKeyBytes)
    (hcomp : primsB.compress = prims.compress) (pk : PublicKey p) (sk : SecretKey p) (E2 : ℝ)
    (htarget : ∀ c, slotsSqDist (toFFTTarget p primsB c sk).1 (toFFTTarget p prims c sk).1 +
      slotsSqDist (toFFTTarget p primsB c sk).2 (toFFTTarget p prims c sk).2 ≤ E2)
    (σlo σhi : ℝ) (hσlo : 1277 / 1000 ≤ σlo) (hleaves : sk.tree.LeavesIn σlo σhi)
    (Lroot Lin μroot μin : ℝ) (hμroot : Lroot ^ 2 ≤ (μroot - 1) * (μroot - 1 - Lroot ^ 2))
    (hμroot' : 1 + Lroot ^ 2 ≤ μroot) (hμin : Lin ^ 2 ≤ (μin - 1) * (μin - 1 - Lin ^ 2))
    (hμin' : 1 + Lin ^ 2 ≤ μin) (hfactors : sk.tree.FactorsLeRoot Lroot Lin) (Z : ℝ)
    (hpost : ∀ c z, PreimageCoeffsLe p.fftDepth Z z →
      fromFFTPreimage p primsB c sk z = fromFFTPreimage p prims c sk z)
    (lam : ℕ) (hlam : 2 ≤ lam) (maxAttempts K : ℕ)
    (hbudget : precisionRate lam σlo *
      (K * maxAttempts * (ffSamplingGrowth p.fftDepth μroot μin * E2)) ≤ Real.log 2 / 2)
    {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (A : OracleComp (unifSpec + signOracleSpec) α) (hK : IsQueryBoundP A IsSignQuery K)
    (T : ℝ≥0∞) (hT : 1 ≤ T) {s : Set α} (hs : MeasurableSet s)
    (hwin : T * (2 : ℝ≥0∞) ^ (-((lam : ℝ) - 1)) <
      𝒟[idealExperiment p primsB pk sk maxAttempts A] s) :
    T * (2 : ℝ≥0∞) ^ (-(lam : ℝ)) <
      𝒟[idealExperiment p prims pk sk maxAttempts A] s +
        K * maxAttempts * preimageTailMass p prims sk Z := by
  have hR := renyiDiv_jointExperiment_le prims primsB hdepth pk sk E2 htarget σlo σhi hσlo
    hleaves Lroot Lin μroot μin hμroot hμroot' hμin hμin' hfactors lam hlam
    maxAttempts K A hK
  rw [simulateQ_jointExperiment_bar, simulateQ_jointExperiment_center] at hR
  have hsqrt : ENNReal.ofReal (Real.exp (precisionRate lam σlo *
      (K * maxAttempts * (ffSamplingGrowth p.fftDepth μroot μin * E2)))) ≤
      (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ((Real.exp_le_exp.2 hbudget).trans (le_of_eq ?_))
    rw [Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  have hH := lt_measure_of_renyiDiv_le_sqrt_two lam hlam T hT _ _ (hR.trans hsqrt) hs hwin
  exact hH.trans_le (evalDist_hybridExperiment_le prims primsB hhash hpkb hcomp pk sk Z hpost
    maxAttempts K A hK hs)

end Falcon
