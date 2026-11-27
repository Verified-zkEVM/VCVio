/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all LatticeCrypto.Falcon.SamplerMinEntropy
public import LatticeCrypto.Falcon.Scheme
public import LatticeCrypto.Falcon.PackedFFT
public import LatticeCrypto.Falcon.SamplerMinEntropy
public import LatticeCrypto.DiscreteGaussian
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.QueryImpl.Compose
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.EvalDist.AnswerMeasure
public import VCVio.OracleComp.SimSemantics.Renyi

/-!
# Falcon signing with an ideal sampler, and the coupled exact / perturbed run

`Primitives.ffSampling` calls `prims.samplerZ : ℝ → ℝ → ProbComp ℤ`, and no `ProbComp` has a
discrete Gaussian output law (`evalDist_ne_discreteGaussianMeasure`). This file makes the sampler a
parameter, so that it can be answered by an oracle with a discrete Gaussian answer measure.

* `ffSamplingWith samp` and `signWith prims salt trap` are `Primitives.ffSampling` and `sign` with
  the sampler, the salt draw and the trapdoor step as parameters, in any monad.
  `ffSamplingWith_samplerZ` and `sign_eq_signWith` recover VCVio's definitions.
* `idealSamplerSpec` is an oracle answering `(μ, σ)` with the discrete Gaussian `D_{σ,μ}` for
  `σ > 0` (`idealSamplerMeasure`). `idealSign prims` is `sign` with every `samplerZ` call
  replaced by a query to it; answering those queries with `prims.samplerZ` gives back
  `sign p prims` (`simulateQ_idealSign_samplerZ`).
* `ffSamplingJoint t u` runs `ffSampling` on two targets at once: every sampler call carries the
  leaf `σ` and the centres computed from `t` and from `u` (`JointQuery`), and its one answer is
  used by both computations. Answering with the centre from `u` gives `ffSamplingWith` on `u`, and
  answering with the centre from `t` gives it on `t` (`simulateQ_ffSamplingJoint_bar`,
  `simulateQ_ffSamplingJoint_center`).
* Along every execution of `ffSamplingJoint t u tree`, the squared differences of the two centres
  of the sampler calls (`jointWeight`) sum to at most `(μroot/2)(μin/2)^(κ-1)` times the squared
  slotwise distance `slotsSqDist` of the targets, when the root factor has every slot at most
  `Lroot` and the other factors at most `Lin` (`pathSum_ffSamplingJoint_root`): a split halves
  the squared distance (`slotsSqDist_splitFFT`), and one LDL step multiplies it by at most `μ`
  (`slotsSqDist_add_adjustTarget`).
-/

public section

open OracleComp OracleSpec LatticeCrypto MeasureTheory
open scoped ENNReal

namespace Falcon

variable {p : Params}

/-! ## Sampler-generic ffSampling and signing -/

/-- `Primitives.ffSampling` with the integer sampler `samp μ σ` as a parameter, in any monad. -/
@[expose] noncomputable def ffSamplingWith {m : Type → Type*} [Monad m] (samp : ℝ → ℝ → m ℤ) :
    (κ : ℕ) → FFTPair κ → FalconTree κ → m (FFTPair κ)
  | 0, (t₀, t₁), .leaf σ => do
    let z₀Re ← samp (RealFFTPoly.re t₀ ⟨0, by omega⟩) σ
    let z₀Im ← samp (RealFFTPoly.im t₀ ⟨0, by omega⟩) σ
    let z₁Re ← samp (RealFFTPoly.re t₁ ⟨0, by omega⟩) σ
    let z₁Im ← samp (RealFFTPoly.im t₁ ⟨0, by omega⟩) σ
    return (RealFFTPoly.pack (Vector.ofFn fun _ => (z₀Re : ℝ)) (Vector.ofFn fun _ => (z₀Im : ℝ)),
      RealFFTPoly.pack (Vector.ofFn fun _ => (z₁Re : ℝ)) (Vector.ofFn fun _ => (z₁Im : ℝ)))
  | k + 1, (t₀, t₁), .node ℓ left right => do
    let z₁Split ← ffSamplingWith samp k (Primitives.splitFFT t₁) right
    let z₁ := Primitives.mergeFFT z₁Split.1 z₁Split.2
    let z₀Split ← ffSamplingWith samp k
      (Primitives.splitFFT (t₀ + Primitives.adjustTarget ℓ t₁ z₁)) left
    return (Primitives.mergeFFT z₀Split.1 z₀Split.2, z₁)

/-- At `prims.samplerZ`, `ffSamplingWith` is `Primitives.ffSampling`. -/
theorem ffSamplingWith_samplerZ (prims : Primitives p) :
    ∀ (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ),
      ffSamplingWith prims.samplerZ κ t tree = Primitives.ffSampling prims κ t tree
  | 0, (t₀, t₁), .leaf σ => rfl
  | k + 1, (t₀, t₁), .node ℓ left right => by
    simp only [ffSamplingWith, Primitives.ffSampling, ffSamplingWith_samplerZ prims k]

variable (p) in
/-- `signAttempt` with the trapdoor step `c ↦ (s₁, s₂)` as a parameter, in any monad. -/
@[expose] noncomputable def attemptWith {m : Type → Type*} [Monad m] (prims : Primitives p)
    (trap : Rq p.n → m (Rq p.n × Rq p.n)) (c : Rq p.n) : m (Option (Rq p.n × Rq p.n)) := do
  let x ← trap c
  if (falconPSF p prims).isShort x then
    return some x
  else
    return none

variable (p) in
/-- `sign` with the salt draw and the trapdoor step `c ↦ (s₁, s₂)` as parameters, in any monad. -/
@[expose] noncomputable def signWith {m : Type → Type*} [Monad m] (prims : Primitives p)
    (salt : m (Bytes 40)) (trap : Rq p.n → m (Rq p.n × Rq p.n)) (pk : PublicKey p)
    (msg : List Byte) : ℕ → m (Option Signature)
  | 0 => return none
  | maxAttempts + 1 => do
    let s ← salt
    let c := prims.hashToPointForPublicKey pk.h s msg
    let r ← attemptWith p prims trap c
    match r with
    | some (_, s₂) =>
        match prims.compress (rqToIntPolyCentered s₂) p.sbytelen with
        | some comp => return (some ⟨s, comp⟩)
        | none => signWith prims salt trap pk msg maxAttempts
    | none => signWith prims salt trap pk msg maxAttempts

/-- `sign` is `signWith` at the uniform salt and the trapdoor sampler of `falconPSF`. -/
theorem sign_eq_signWith (prims : Primitives p) (pk : PublicKey p) (sk : SecretKey p)
    (msg : List Byte) : ∀ maxAttempts : ℕ,
      sign p prims pk sk msg maxAttempts =
        signWith p prims ($ᵗ (Bytes 40)) ((falconPSF p prims).trapdoorSample pk sk) pk msg
          maxAttempts
  | 0 => rfl
  | n + 1 => by
    have h : ∀ c, signAttempt p prims pk sk c =
        attemptWith p prims ((falconPSF p prims).trapdoorSample pk sk) c := fun _ => rfl
    simp only [sign, signWith, h, sign_eq_signWith prims pk sk msg n]
    refine bind_congr fun s => bind_congr fun r => ?_
    rcases r with _ | ⟨_, s₂⟩
    · rfl
    · cases prims.compress (rqToIntPolyCentered s₂) p.sbytelen <;> rfl

variable (p) in
/-- The trapdoor step of `falconPSF` with the integer sampler as a parameter. -/
@[expose] noncomputable def trapdoorWith {m : Type → Type*} [Monad m] (prims : Primitives p)
    (sk : SecretKey p) (samp : ℝ → ℝ → m ℤ) (c : Rq p.n) : m (Rq p.n × Rq p.n) := do
  let z ← ffSamplingWith samp p.fftDepth (toFFTTarget p prims c sk) sk.tree
  return fromFFTPreimage p prims c sk z

/-- At `prims.samplerZ`, `trapdoorWith` is the trapdoor sampler of `falconPSF`. -/
theorem trapdoorWith_samplerZ (prims : Primitives p) (pk : PublicKey p) (sk : SecretKey p) :
    trapdoorWith p prims sk prims.samplerZ = (falconPSF p prims).trapdoorSample pk sk := by
  funext c
  simp only [trapdoorWith, ffSamplingWith_samplerZ]
  rfl

/-- `attemptWith` commutes with simulation. -/
theorem simulateQ_attemptWith {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec m) (prims : Primitives p)
    (trap : Rq p.n → OracleComp spec (Rq p.n × Rq p.n)) (c : Rq p.n) :
    simulateQ impl (attemptWith p prims trap c) =
      attemptWith p prims (fun c => simulateQ impl (trap c)) c := by
  simp only [attemptWith, simulateQ_bind]
  refine bind_congr fun x => ?_
  split_ifs <;> simp

/-- `signWith` commutes with simulation. -/
theorem simulateQ_signWith {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec m) (prims : Primitives p)
    (salt : OracleComp spec (Bytes 40)) (trap : Rq p.n → OracleComp spec (Rq p.n × Rq p.n))
    (pk : PublicKey p) (msg : List Byte) : ∀ maxAttempts : ℕ,
      simulateQ impl (signWith p prims salt trap pk msg maxAttempts) =
        signWith p prims (simulateQ impl salt) (fun c => simulateQ impl (trap c)) pk msg
          maxAttempts
  | 0 => by simp [signWith]
  | n + 1 => by
    simp only [signWith, simulateQ_bind, simulateQ_attemptWith]
    refine bind_congr fun s => bind_congr fun r => ?_
    rcases r with _ | ⟨_, s₂⟩
    · exact simulateQ_signWith impl prims salt trap pk msg n
    · dsimp only
      split
      · rw [simulateQ_pure]
      · exact simulateQ_signWith impl prims salt trap pk msg n

/-- `ffSamplingWith` commutes with simulation. -/
theorem simulateQ_ffSamplingWith {ι : Type} {spec : OracleSpec ι} {m : Type → Type*} [Monad m]
    [LawfulMonad m] (impl : QueryImpl spec m) (samp : ℝ → ℝ → OracleComp spec ℤ) :
    ∀ (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ),
      simulateQ impl (ffSamplingWith samp κ t tree) =
        ffSamplingWith (fun μ σ => simulateQ impl (samp μ σ)) κ t tree
  | 0, (t₀, t₁), .leaf σ => by simp [ffSamplingWith]
  | k + 1, (t₀, t₁), .node ℓ left right => by
    simp [ffSamplingWith, simulateQ_ffSamplingWith impl samp k]

/-! ## The ideal sampler -/

/-- Queries `(μ, σ)` to an ideal integer sampler. -/
@[expose] def idealSamplerSpec : OracleSpec (ℝ × ℝ) := (ℝ × ℝ) →ₒ ℤ

instance (q : ℝ × ℝ) : Countable (idealSamplerSpec.Range q) := inferInstanceAs (Countable ℤ)

/-- The answer law of the ideal sampler: the discrete Gaussian `D_{σ,μ}` for `σ > 0`. The point
mass at `0` for `σ ≤ 0` only makes the answer measure total; trees with leaves in a positive
range never query it. -/
@[expose] noncomputable def idealSamplerMeasure (μ σ : ℝ) : Measure ℤ :=
  if 0 < σ then discreteGaussianMeasure σ μ else Measure.dirac 0

theorem isProbabilityMeasure_idealSamplerMeasure (μ σ : ℝ) :
    IsProbabilityMeasure (idealSamplerMeasure μ σ) := by
  unfold idealSamplerMeasure
  split_ifs with h
  · exact isProbabilityMeasure_discreteGaussianMeasure σ μ h
  · infer_instance

/-- For `σ > 0` the ideal sampler answers with `D_{σ,μ}`. -/
theorem idealSamplerMeasure_of_pos {μ σ : ℝ} (h : 0 < σ) :
    idealSamplerMeasure μ σ = discreteGaussianMeasure σ μ := ite_eq_left h

noncomputable instance : OracleSpec.AnswerMeasure idealSamplerSpec :=
  @PFunctor.AnswerMeasure.mk idealSamplerSpec.toPFunctor (fun _ => ⊤)
    (fun q => idealSamplerMeasure q.1 q.2)
    (fun q => isProbabilityMeasure_idealSamplerMeasure q.1 q.2)

/-- A query `(μ, σ)` to the ideal sampler, alongside uniform coins. -/
@[expose] noncomputable def idealSamplerQuery (μ σ : ℝ) :
    OracleComp (unifSpec + idealSamplerSpec) ℤ :=
  liftM ((unifSpec + idealSamplerSpec).query (Sum.inr (μ, σ)))

/-- Simulating an ideal sampler query runs the handler at that query. -/
theorem simulateQ_idealSamplerQuery {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (unifSpec + idealSamplerSpec) m) (μ σ : ℝ) :
    simulateQ impl (idealSamplerQuery μ σ) = impl (Sum.inr (μ, σ)) :=
  simulateQ_spec_query impl (Sum.inr (μ, σ))

/-- Uniform coins forwarded into a specification with more oracles. -/
@[expose] noncomputable def unifLift {ι : Type} (spec : OracleSpec.{0, 0} ι) :
    QueryImpl unifSpec (OracleComp (unifSpec + spec)) :=
  QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))

variable (p) in
/-- **Falcon signing with an ideal sampler.** `sign` with every `samplerZ μ σ` call replaced by
a query to the ideal sampler, which answers with `D_{σ,μ}`. -/
@[expose] noncomputable def idealSign (prims : Primitives p) (pk : PublicKey p) (sk : SecretKey p)
    (msg : List Byte) (maxAttempts : ℕ) :
    OracleComp (unifSpec + idealSamplerSpec) (Option Signature) :=
  signWith p prims (liftComp ($ᵗ (Bytes 40)) (unifSpec + idealSamplerSpec))
    (trapdoorWith p prims sk idealSamplerQuery) pk msg maxAttempts

/-- Answering the ideal sampler with `prims.samplerZ` gives back VCVio's `sign`. -/
theorem simulateQ_idealSign_samplerZ (prims : Primitives p) (pk : PublicKey p) (sk : SecretKey p)
    (msg : List Byte) (maxAttempts : ℕ) :
    simulateQ (QueryImpl.id' unifSpec +
        (show QueryImpl idealSamplerSpec ProbComp from fun q => prims.samplerZ q.1 q.2))
      (idealSign p prims pk sk msg maxAttempts) = sign p prims pk sk msg maxAttempts := by
  have hsalt : simulateQ (QueryImpl.id' unifSpec +
        (show QueryImpl idealSamplerSpec ProbComp from fun q => prims.samplerZ q.1 q.2))
      (liftComp ($ᵗ (Bytes 40)) (unifSpec + idealSamplerSpec)) = $ᵗ (Bytes 40) := by
    rw [QueryImpl.simulateQ_add_liftComp_left, simulateQ_id']
  have htrap : (fun c => simulateQ (QueryImpl.id' unifSpec +
        (show QueryImpl idealSamplerSpec ProbComp from fun q => prims.samplerZ q.1 q.2))
      (trapdoorWith p prims sk idealSamplerQuery c)) = trapdoorWith p prims sk prims.samplerZ := by
    funext c
    simp only [trapdoorWith, simulateQ_bind, simulateQ_pure, simulateQ_ffSamplingWith,
      simulateQ_idealSamplerQuery]
    rfl
  rw [idealSign, simulateQ_signWith, hsalt, htrap, trapdoorWith_samplerZ prims pk sk,
    sign_eq_signWith]

/-! ## The coupled run -/

/-- A sampler call of the coupled run: the leaf standard deviation and the two centres. -/
structure JointQuery where
  /-- The leaf standard deviation. -/
  sigma : ℝ
  /-- The centre computed from the reference target. -/
  center : ℝ
  /-- The centre computed from the perturbed target. -/
  centerBar : ℝ

/-- Sampler calls of the coupled run. -/
@[expose] def jointSamplerSpec : OracleSpec JointQuery := JointQuery →ₒ ℤ

instance (q : JointQuery) : Countable (jointSamplerSpec.Range q) := inferInstanceAs (Countable ℤ)

instance : ∀ t, Countable ((unifSpec + jointSamplerSpec).Range t)
  | .inl n => inferInstanceAs (Countable (Fin (n + 1)))
  | .inr _ => inferInstanceAs (Countable ℤ)

/-- One sampler call of the coupled run. -/
@[expose] noncomputable def jointQuery (q : JointQuery) :
    OracleComp (unifSpec + jointSamplerSpec) ℤ :=
  liftM ((unifSpec + jointSamplerSpec).query (Sum.inr q))

/-- Simulating a coupled call runs the handler at that call. -/
theorem simulateQ_jointQuery {m : Type → Type*} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (unifSpec + jointSamplerSpec) m) (q : JointQuery) :
    simulateQ impl (jointQuery q) = impl (Sum.inr q) :=
  simulateQ_spec_query impl (Sum.inr q)

/-- **The coupled ffSampling run** on a reference target `t` and a perturbed target `u`: each
sampler call carries the leaf and both centres, and its answer is used on both sides. -/
@[expose] noncomputable def ffSamplingJoint :
    (κ : ℕ) → FFTPair κ → FFTPair κ → FalconTree κ →
      OracleComp (unifSpec + jointSamplerSpec) (FFTPair κ)
  | 0, (t₀, t₁), (u₀, u₁), .leaf σ => do
    let z₀Re ← jointQuery ⟨σ, RealFFTPoly.re t₀ ⟨0, by omega⟩, RealFFTPoly.re u₀ ⟨0, by omega⟩⟩
    let z₀Im ← jointQuery ⟨σ, RealFFTPoly.im t₀ ⟨0, by omega⟩, RealFFTPoly.im u₀ ⟨0, by omega⟩⟩
    let z₁Re ← jointQuery ⟨σ, RealFFTPoly.re t₁ ⟨0, by omega⟩, RealFFTPoly.re u₁ ⟨0, by omega⟩⟩
    let z₁Im ← jointQuery ⟨σ, RealFFTPoly.im t₁ ⟨0, by omega⟩, RealFFTPoly.im u₁ ⟨0, by omega⟩⟩
    return (RealFFTPoly.pack (Vector.ofFn fun _ => (z₀Re : ℝ)) (Vector.ofFn fun _ => (z₀Im : ℝ)),
      RealFFTPoly.pack (Vector.ofFn fun _ => (z₁Re : ℝ)) (Vector.ofFn fun _ => (z₁Im : ℝ)))
  | k + 1, (t₀, t₁), (u₀, u₁), .node ℓ left right => do
    let z₁Split ← ffSamplingJoint k (Primitives.splitFFT t₁) (Primitives.splitFFT u₁) right
    let z₁ := Primitives.mergeFFT z₁Split.1 z₁Split.2
    let z₀Split ← ffSamplingJoint k
      (Primitives.splitFFT (t₀ + Primitives.adjustTarget ℓ t₁ z₁))
      (Primitives.splitFFT (u₀ + Primitives.adjustTarget ℓ u₁ z₁)) left
    return (Primitives.mergeFFT z₀Split.1 z₀Split.2, z₁)

/-- The ideal sampler answering each coupled call at the centre `centre q`: the perturbed centre
`JointQuery.centerBar` or the reference centre `JointQuery.center`. -/
@[expose] noncomputable def jointAnswer (centre : JointQuery → ℝ) :
    QueryImpl (unifSpec + jointSamplerSpec) (OracleComp (unifSpec + idealSamplerSpec)) :=
  unifLift idealSamplerSpec +
    (show QueryImpl jointSamplerSpec (OracleComp (unifSpec + idealSamplerSpec)) from
      fun q => idealSamplerQuery (centre q) q.sigma)

/-- `jointAnswer centre` answers a coupled call at `centre q`. -/
theorem jointAnswer_inr (centre : JointQuery → ℝ) (q : JointQuery) :
    jointAnswer centre (Sum.inr q) = idealSamplerQuery (centre q) q.sigma := rfl

/-- Answered at the perturbed centres, the coupled run is ffSampling on the perturbed target. -/
theorem simulateQ_ffSamplingJoint_bar :
    ∀ (κ : ℕ) (t u : FFTPair κ) (tree : FalconTree κ),
      simulateQ (jointAnswer JointQuery.centerBar) (ffSamplingJoint κ t u tree) =
        ffSamplingWith idealSamplerQuery κ u tree
  | 0, (t₀, t₁), (u₀, u₁), .leaf σ => by
    simp only [ffSamplingJoint, ffSamplingWith, simulateQ_bind, simulateQ_pure,
      simulateQ_jointQuery, jointAnswer_inr]
  | k + 1, (t₀, t₁), (u₀, u₁), .node ℓ left right => by
    simp only [ffSamplingJoint, ffSamplingWith, simulateQ_bind, simulateQ_pure,
      simulateQ_ffSamplingJoint_bar k]

/-- Answered at the reference centres, the coupled run is ffSampling on the reference target. -/
theorem simulateQ_ffSamplingJoint_center :
    ∀ (κ : ℕ) (t u : FFTPair κ) (tree : FalconTree κ),
      simulateQ (jointAnswer JointQuery.center) (ffSamplingJoint κ t u tree) =
        ffSamplingWith idealSamplerQuery κ t tree
  | 0, (t₀, t₁), (u₀, u₁), .leaf σ => by
    simp only [ffSamplingJoint, ffSamplingWith, simulateQ_bind, simulateQ_pure,
      simulateQ_jointQuery, jointAnswer_inr]
  | k + 1, (t₀, t₁), (u₀, u₁), .node ℓ left right => by
    simp only [ffSamplingJoint, ffSamplingWith, simulateQ_bind, simulateQ_pure,
      simulateQ_ffSamplingJoint_center k]

/-! ## Centre error summed along the coupled run -/

namespace RealFFTPoly

variable {k : ℕ}

theorem coord_sub (a b : RealFFTPoly k) (j : Fin (2 ^ k)) :
    coord (a - b) j = coord a j - coord b j := by
  apply Complex.ext
  · simp only [coord_re, Complex.sub_re]
    exact LatticeCrypto.Poly.get_sub (Coeff := ℝ) a b _
  · simp only [coord_im, Complex.sub_im]
    exact LatticeCrypto.Poly.get_sub (Coeff := ℝ) a b _

/-- The even part of `splitFFT` averages the two children of a slot. -/
theorem coord_splitFFT_fst (f : RealFFTPoly (k + 1)) (i : Fin (2 ^ k)) :
    coord (Primitives.splitFFT f).1 i =
      (coord f ⟨2 * i.1, by omega⟩ + coord f ⟨2 * i.1 + 1, by omega⟩) / 2 := by
  apply Complex.ext <;> simp [Primitives.splitFFT]

/-- The odd part of `splitFFT` is the half-difference of the two children of a slot, rotated by
`exp(-i · splitAngle i)`. -/
theorem coord_splitFFT_snd (f : RealFFTPoly (k + 1)) (i : Fin (2 ^ k)) :
    coord (Primitives.splitFFT f).2 i =
      (coord f ⟨2 * i.1, by omega⟩ - coord f ⟨2 * i.1 + 1, by omega⟩) / 2 *
        ⟨Real.cos (Primitives.splitAngle i), -Real.sin (Primitives.splitAngle i)⟩ := by
  apply Complex.ext <;> simp [Primitives.splitFFT, Complex.mul_re, Complex.mul_im]
  ring

theorem norm_cos_neg_sin (θ : ℝ) : ‖(⟨Real.cos θ, -Real.sin θ⟩ : ℂ)‖ = 1 := by
  have h : Complex.normSq ⟨Real.cos θ, -Real.sin θ⟩ = 1 := by
    rw [Complex.normSq_mk]; nlinarith [Real.cos_sq_add_sin_sq θ]
  rw [Complex.norm_def, h, Real.sqrt_one]

end RealFFTPoly

/-- Every slot of every LDL factor `ℓ` of the tree has modulus at most `L`. -/
@[expose] def FalconTree.FactorsLe : {κ : ℕ} → FalconTree κ → ℝ → Prop
  | _, .leaf _, _ => True
  | _, .node ℓ left right, L =>
      (∀ j, ‖RealFFTPoly.coord ℓ j‖ ≤ L) ∧ left.FactorsLe L ∧ right.FactorsLe L

/-- The squared slotwise distance `∑ⱼ ‖f j - g j‖²`. -/
@[expose] noncomputable def slotsSqDist {k : ℕ} (f g : RealFFTPoly k) : ℝ :=
  ∑ j, ‖RealFFTPoly.coord f j - RealFFTPoly.coord g j‖ ^ 2

/-- The root factor has every slot at most `Lroot`, and every factor below it every slot at most
`Lin`. -/
@[expose] def FalconTree.FactorsLeRoot : {κ : ℕ} → FalconTree κ → ℝ → ℝ → Prop
  | _, .leaf _, _, _ => True
  | _, .node ℓ left right, Lroot, Lin =>
      (∀ j, ‖RealFFTPoly.coord ℓ j‖ ≤ Lroot) ∧ left.FactorsLe Lin ∧ right.FactorsLe Lin

/-- Every leaf of the tree is at least `σlo` (no upper bound). -/
@[expose] def JointLeafGe (σlo : ℝ) : ℕ ⊕ JointQuery → Prop
  | .inl _ => True
  | .inr q => σlo ≤ q.sigma

/-- The weight of a query of the coupled run: `0` for uniform coins, the squared centre
difference for a sampler call. -/
@[expose] def jointWeight : ℕ ⊕ JointQuery → ℝ
  | .inl _ => 0
  | .inr q => (q.centerBar - q.center) ^ 2

/-- Along every execution of the coupled run, every leaf is at least `σlo`. -/
theorem allQueriesSatisfy_ffSamplingJoint_leafGe {σlo σhi : ℝ} :
    ∀ (κ : ℕ) (t u : FFTPair κ) (tree : FalconTree κ), tree.LeavesIn σlo σhi →
      AllQueriesSatisfy (ffSamplingJoint κ t u tree) (JointLeafGe σlo)
  | 0, (t₀, t₁), (u₀, u₁), .leaf σ, hleaf => by
    obtain ⟨hσ, -⟩ : σlo ≤ σ ∧ σ ≤ σhi := hleaf
    have hq : ∀ q : JointQuery, q.sigma = σ →
        AllQueriesSatisfy (jointQuery q) (JointLeafGe σlo) := fun q hq =>
      (allQueriesSatisfy_query_iff _ _).2 (by change σlo ≤ q.sigma; rw [hq]; exact hσ)
    simp only [ffSamplingJoint]
    exact allQueriesSatisfy_bind (hq _ rfl) fun _ => allQueriesSatisfy_bind (hq _ rfl) fun _ =>
      allQueriesSatisfy_bind (hq _ rfl) fun _ => allQueriesSatisfy_bind (hq _ rfl) fun _ =>
        allQueriesSatisfy_pure _ _
  | k + 1, (t₀, t₁), (u₀, u₁), .node ℓ left right, hleaf => by
    obtain ⟨hlo, hro⟩ : left.LeavesIn σlo σhi ∧ right.LeavesIn σlo σhi := hleaf
    simp only [ffSamplingJoint]
    exact allQueriesSatisfy_bind (allQueriesSatisfy_ffSamplingJoint_leafGe k _ _ right hro)
      fun _ => allQueriesSatisfy_bind (allQueriesSatisfy_ffSamplingJoint_leafGe k _ _ left hlo)
        fun _ => allQueriesSatisfy_pure _ _

/-- One step of the LDL recursion: `‖a + ℓ b‖² + ‖b‖² ≤ μ (‖a‖² + ‖b‖²)` for `‖ℓ‖ ≤ L`, when
`L² ≤ (μ - 1)(μ - 1 - L²)` and `1 + L² ≤ μ`. -/
theorem norm_add_mul_sq_add_sq_le {a b ℓ : ℂ} {L μ : ℝ} (hℓ : ‖ℓ‖ ≤ L)
    (hμ : L ^ 2 ≤ (μ - 1) * (μ - 1 - L ^ 2)) (hμ' : 1 + L ^ 2 ≤ μ) :
    ‖a + ℓ * b‖ ^ 2 + ‖b‖ ^ 2 ≤ μ * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hℓ
  have h1 : ‖a + ℓ * b‖ ≤ ‖a‖ + L * ‖b‖ :=
    (norm_add_le _ _).trans (by rw [norm_mul]; gcongr)
  have h2 : ‖a + ℓ * b‖ ^ 2 ≤ (‖a‖ + L * ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  set x := ‖a‖
  set y := ‖b‖
  have hC : 0 ≤ μ - 1 - L ^ 2 := by linarith
  have hq : 0 ≤ (μ - 1) * x ^ 2 - 2 * L * x * y + (μ - 1 - L ^ 2) * y ^ 2 := by
    rcases (show 0 ≤ μ - 1 by nlinarith).lt_or_eq with hA | hA
    · have e : (μ - 1) * ((μ - 1) * x ^ 2 - 2 * L * x * y + (μ - 1 - L ^ 2) * y ^ 2) =
          ((μ - 1) * x - L * y) ^ 2 + ((μ - 1) * (μ - 1 - L ^ 2) - L ^ 2) * y ^ 2 := by ring
      have h0 : 0 ≤ ((μ - 1) * x - L * y) ^ 2 + ((μ - 1) * (μ - 1 - L ^ 2) - L ^ 2) * y ^ 2 :=
        add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
      rw [← e] at h0
      exact (mul_nonneg_iff_of_pos_left hA).1 h0
    · have hL0 : L = 0 := by rw [← hA] at hμ; nlinarith
      rw [← hA, hL0]; simp
  nlinarith

/-- A sum over `2^(k+1)` slots, by pairs of even and odd slots. -/
theorem sum_two_pow_succ {M : Type*} [AddCommMonoid M] {k : ℕ} (F : Fin (2 ^ (k + 1)) → M) :
    ∑ j, F j = ∑ i : Fin (2 ^ k), (F ⟨2 * i.1, by omega⟩ + F ⟨2 * i.1 + 1, by omega⟩) := by
  rw [← (finProdFinEquiv.trans (finCongr (pow_succ 2 k).symm)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  congr 2
  · ext; simp [finProdFinEquiv]
  · ext; simp [finProdFinEquiv]; ring

/-- `splitFFT` halves the squared slotwise distance. -/
theorem slotsSqDist_splitFFT {k : ℕ} (f g : RealFFTPoly (k + 1)) :
    slotsSqDist (Primitives.splitFFT f).1 (Primitives.splitFFT g).1 +
      slotsSqDist (Primitives.splitFFT f).2 (Primitives.splitFFT g).2 = slotsSqDist f g / 2 := by
  rw [slotsSqDist, slotsSqDist, slotsSqDist, sum_two_pow_succ, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RealFFTPoly.coord_splitFFT_fst, RealFFTPoly.coord_splitFFT_fst,
    RealFFTPoly.coord_splitFFT_snd, RealFFTPoly.coord_splitFFT_snd]
  set r : ℂ := ⟨Real.cos (Primitives.splitAngle i), -Real.sin (Primitives.splitAngle i)⟩
  set a₀ := RealFFTPoly.coord f ⟨2 * i.1, by omega⟩
  set a₁ := RealFFTPoly.coord f ⟨2 * i.1 + 1, by omega⟩
  set b₀ := RealFFTPoly.coord g ⟨2 * i.1, by omega⟩
  set b₁ := RealFFTPoly.coord g ⟨2 * i.1 + 1, by omega⟩
  have e1 : (a₀ + a₁) / 2 - (b₀ + b₁) / 2 = (a₀ - b₀ + (a₁ - b₁)) / 2 := by ring
  have e2 : (a₀ - a₁) / 2 * r - (b₀ - b₁) / 2 * r = (a₀ - b₀ - (a₁ - b₁)) / 2 * r := by ring
  rw [e1, e2, norm_mul, RealFFTPoly.norm_cos_neg_sin, mul_one, norm_div, norm_div,
    Complex.norm_ofNat]
  set x := a₀ - b₀
  set y := a₁ - b₁
  have hp := parallelogram_law_with_norm ℝ x y
  calc (‖x + y‖ / 2) ^ 2 + (‖x - y‖ / 2) ^ 2 = (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 4 := by ring
    _ = (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by rw [hp]; ring

/-- The adjusted targets `t₀ + ℓ ⊙ (t₁ - z₁)` of two runs with the same `z₁`, in squared slotwise
distance. -/
theorem slotsSqDist_add_adjustTarget {k : ℕ} {L μ : ℝ} {t₀ u₀ t₁ u₁ ℓ z : RealFFTPoly k}
    (hℓ : ∀ j, ‖RealFFTPoly.coord ℓ j‖ ≤ L) (hμ : L ^ 2 ≤ (μ - 1) * (μ - 1 - L ^ 2))
    (hμ' : 1 + L ^ 2 ≤ μ) :
    slotsSqDist (u₀ + Primitives.adjustTarget ℓ u₁ z) (t₀ + Primitives.adjustTarget ℓ t₁ z) +
      slotsSqDist u₁ t₁ ≤ μ * (slotsSqDist u₀ t₀ + slotsSqDist u₁ t₁) := by
  simp only [slotsSqDist, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : RealFFTPoly.coord (u₀ + Primitives.adjustTarget ℓ u₁ z) j -
      RealFFTPoly.coord (t₀ + Primitives.adjustTarget ℓ t₁ z) j =
      (RealFFTPoly.coord u₀ j - RealFFTPoly.coord t₀ j) +
        RealFFTPoly.coord ℓ j * (RealFFTPoly.coord u₁ j - RealFFTPoly.coord t₁ j) := by
    simp only [Primitives.adjustTarget, RealFFTPoly.coord_add, RealFFTPoly.coord_mulFFT,
      RealFFTPoly.coord_sub]
    ring
  rw [e]
  exact norm_add_mul_sq_add_sq_le (hℓ j) hμ hμ'

/-- A coupled run on a single slot charges the squared slotwise distance of its targets. -/
theorem pathSum_ffSamplingJoint_leaf (t u : FFTPair 0) (σ : ℝ) :
    PathSum jointWeight (ffSamplingJoint 0 t u (.leaf σ))
      (slotsSqDist u.1 t.1 + slotsSqDist u.2 t.2) := by
  obtain ⟨t₀, t₁⟩ := t
  obtain ⟨u₀, u₁⟩ := u
  have hone : ∀ a b : RealFFTPoly 0, slotsSqDist a b =
      (RealFFTPoly.re a ⟨0, by omega⟩ - RealFFTPoly.re b ⟨0, by omega⟩) ^ 2 +
        (RealFFTPoly.im a ⟨0, by omega⟩ - RealFFTPoly.im b ⟨0, by omega⟩) ^ 2 := by
    intro a b
    rw [slotsSqDist, Fintype.sum_eq_single ⟨0, by omega⟩ fun j hj => absurd (Fin.ext (by
      have h := j.2; simp only [pow_zero, Nat.lt_one_iff] at h; exact h)) hj, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, RealFFTPoly.coord_re, RealFFTPoly.coord_im]
    ring
  simp only [ffSamplingJoint]
  refine .query_bind (Sum.inr _) _ fun _ => .query_bind (Sum.inr _) _ fun _ =>
    .query_bind (Sum.inr _) _ fun _ => .query_bind (Sum.inr _) _ fun _ => .pure _ ?_
  simp only [jointWeight, hone]
  linarith

/-- One node of the coupled run: if both subtrees charge at most `C` times the squared slotwise
distance of their targets, the node charges at most `(μ/2) · C` times that of its targets. -/
theorem pathSum_ffSamplingJoint_node {k : ℕ} {L μ C : ℝ} (hC : 0 ≤ C)
    (hμ : L ^ 2 ≤ (μ - 1) * (μ - 1 - L ^ 2)) (hμ' : 1 + L ^ 2 ≤ μ) (ℓ : RealFFTPoly (k + 1))
    (left right : FalconTree k) (hℓ : ∀ j, ‖RealFFTPoly.coord ℓ j‖ ≤ L)
    (hleft : ∀ t u : FFTPair k, PathSum jointWeight (ffSamplingJoint k t u left)
      (C * (slotsSqDist u.1 t.1 + slotsSqDist u.2 t.2)))
    (hright : ∀ t u : FFTPair k, PathSum jointWeight (ffSamplingJoint k t u right)
      (C * (slotsSqDist u.1 t.1 + slotsSqDist u.2 t.2)))
    (t u : FFTPair (k + 1)) :
    PathSum jointWeight (ffSamplingJoint (k + 1) t u (.node ℓ left right))
      (μ / 2 * C * (slotsSqDist u.1 t.1 + slotsSqDist u.2 t.2)) := by
  obtain ⟨t₀, t₁⟩ := t
  obtain ⟨u₀, u₁⟩ := u
  set D₀ := slotsSqDist u₀ t₀
  set D₁ := slotsSqDist u₁ t₁
  have hL : ∀ z₁ : FFTPair k, PathSum jointWeight (ffSamplingJoint k
      (Primitives.splitFFT (t₀ + Primitives.adjustTarget ℓ t₁ (Primitives.mergeFFT z₁.1 z₁.2)))
      (Primitives.splitFFT (u₀ + Primitives.adjustTarget ℓ u₁ (Primitives.mergeFFT z₁.1 z₁.2)))
      left) (C * ((μ * (D₀ + D₁) - D₁) / 2)) := fun z₁ => by
    refine (hleft _ _).weaken ?_
    rw [slotsSqDist_splitFFT]
    have := slotsSqDist_add_adjustTarget (t₀ := t₀) (u₀ := u₀) (t₁ := t₁) (u₁ := u₁)
      (z := Primitives.mergeFFT z₁.1 z₁.2) hℓ hμ hμ'
    gcongr
    linarith
  simp only [ffSamplingJoint]
  refine ((hright _ _).bind fun z₁ => (hL z₁).bind fun _ => PathSum.pure _ le_rfl).weaken
    (le_of_eq ?_)
  rw [slotsSqDist_splitFFT]
  ring

/-- **Summed centre error, uniform factor bound.** If every factor slot is at most `L` and
`L² ≤ (μ - 1)(μ - 1 - L²)`, `1 + L² ≤ μ`, the squared centre differences along every execution
of the coupled run sum to at most `(μ/2)^κ` times the squared slotwise distance of the targets. -/
theorem pathSum_ffSamplingJoint {L μ : ℝ} (hμ : L ^ 2 ≤ (μ - 1) * (μ - 1 - L ^ 2))
    (hμ' : 1 + L ^ 2 ≤ μ) :
    ∀ (κ : ℕ) (t u : FFTPair κ) (tree : FalconTree κ), tree.FactorsLe L →
      PathSum jointWeight (ffSamplingJoint κ t u tree)
        ((μ / 2) ^ κ * (slotsSqDist u.1 t.1 + slotsSqDist u.2 t.2))
  | 0, t, u, .leaf σ, _ => by
    rw [pow_zero, one_mul]
    exact pathSum_ffSamplingJoint_leaf t u σ
  | k + 1, t, u, .node ℓ left right, hfac => by
    obtain ⟨hℓ, hfl, hfr⟩ := hfac
    have hμ0 : 0 ≤ μ := by nlinarith
    rw [pow_succ']
    exact pathSum_ffSamplingJoint_node (by positivity) hμ hμ' ℓ left right hℓ
      (fun t u => pathSum_ffSamplingJoint hμ hμ' k t u left hfl)
      (fun t u => pathSum_ffSamplingJoint hμ hμ' k t u right hfr) t u

/-- **Summed centre error, root and inner factor bounds.** With the root factor bounded by
`Lroot` and the others by `Lin`, the squared centre differences along every execution sum to at
most `(μroot/2)(μin/2)^(κ-1)` times the squared slotwise distance of the targets. -/
theorem pathSum_ffSamplingJoint_root {Lroot Lin μroot μin : ℝ}
    (hμroot : Lroot ^ 2 ≤ (μroot - 1) * (μroot - 1 - Lroot ^ 2))
    (hμroot' : 1 + Lroot ^ 2 ≤ μroot) (hμin : Lin ^ 2 ≤ (μin - 1) * (μin - 1 - Lin ^ 2))
    (hμin' : 1 + Lin ^ 2 ≤ μin) (κ : ℕ) (t u : FFTPair (κ + 1)) (tree : FalconTree (κ + 1))
    (htree : tree.FactorsLeRoot Lroot Lin) :
    PathSum jointWeight (ffSamplingJoint (κ + 1) t u tree)
      (μroot / 2 * (μin / 2) ^ κ * (slotsSqDist u.1 t.1 + slotsSqDist u.2 t.2)) := by
  match tree, htree with
  | .node ℓ left right, ⟨hℓ, hfl, hfr⟩ =>
    have hμ0 : 0 ≤ μin := by nlinarith
    exact pathSum_ffSamplingJoint_node (by positivity) hμroot hμroot' ℓ left right hℓ
      (fun t u => pathSum_ffSamplingJoint hμin hμin' κ t u left hfl)
      (fun t u => pathSum_ffSamplingJoint hμin hμin' κ t u right hfr) t u

end Falcon
