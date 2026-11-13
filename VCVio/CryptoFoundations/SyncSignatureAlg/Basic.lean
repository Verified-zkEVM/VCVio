/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import Mathlib.Logic.Function.Basic
public import VCVio.OracleComp.ProbCompLift

/-! # Synchronized signature algorithms

Epoch-indexed signing separates correctness for each generated key from the joint
key-generation/signing experiment. Returned failure, rejection and missing execution mass count
against the stated error in both observations.
-/

public section


open ENNReal

universe v

/-- Epoch-indexed signature algorithms with system configuration fixed by the scheme instance. -/
structure SyncSignatureAlg (m : Type → Type v) [Monad m] (M PK SK S E : Type) where
  /-- Generate a public and secret key for this scheme instance. -/
  keygen : m (PK × SK)
  /-- Sign at a valid epoch; a returned `none` is an explicit signing failure. -/
  sign : SK → E → M → m (Option S)
  /-- Deterministically verify a signature at the supplied epoch. -/
  verify : PK → E → M → S → Bool

namespace SyncSignatureAlg

variable {m : Type → Type v} [Monad m] {M PK SK S E : Type}

/-- The Boolean observation of signing: explicit failure is rejected. -/
@[expose] def accepts (alg : SyncSignatureAlg m M PK SK S E)
    (pk : PK) (ep : E) (msg : M) : Option S → Bool
  | none => false
  | some sig => alg.verify pk ep msg sig

/-- A returned signing failure is never accepted. -/
@[simp] theorem accepts_none (alg : SyncSignatureAlg m M PK SK S E)
    (pk : PK) (ep : E) (msg : M) : alg.accepts pk ep msg none = false := rfl

/-- Successful returned signatures are observed by deterministic verification. -/
@[simp] theorem accepts_some (alg : SyncSignatureAlg m M PK SK S E)
    (pk : PK) (ep : E) (msg : M) (sig : S) :
    alg.accepts pk ep msg (some sig) = alg.verify pk ep msg sig := rfl

/-- A key pair is producible exactly when it has positive mass in the chosen runtime. -/
@[expose] def Generated (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) : Prop :=
  0 < runtime.evalDist ((fun ks' => ks' = ks) <$> alg.keygen) {True}

/-- The unnormalized probability of successful verification for a fixed key pair. -/
@[expose] noncomputable def successMass (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) : ℝ≥0∞ :=
  runtime.evalDist (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) {true}

/-- The measure singleton agrees with the runtime's discrete successful-output probability. -/
theorem successMass_eq_probability (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) :
    alg.successMass runtime ks ep msg =
      runtime.evalDist (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) {true} := rfl

/-- Successful verification has subprobability mass at most one. -/
theorem successMass_le_one (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) :
    alg.successMass runtime ks ep msg ≤ 1 := by
  rw [successMass_eq_probability]
  exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans
    (runtime.evalDist_apply_univ_le_one _)

/-- A signing-and-verification observation concentrated on rejection has no success mass. -/
theorem successMass_eq_zero_of_rejection (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M)
    (h : runtime.evalDist (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) =
      MeasureTheory.Measure.dirac false) :
    alg.successMass runtime ks ep msg = 0 := by
  simp [successMass, h]

/-- A signer with entirely missing output mass has no successful verification mass. -/
theorem successMass_eq_zero_of_failure (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M)
    (h : runtime.evalDist (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) = 0) :
    alg.successMass runtime ks ep msg = 0 := by
  simp [successMass, h]

/-- Correctness for every producible key pair, epoch and message of this scheme instance.
Returned failure, verification rejection and missing mass all count against `δ`. -/
@[expose] def CompletePerKey (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) : Prop :=
  ∀ ks, alg.Generated runtime ks → ∀ ep msg,
    1 - δ ≤ alg.successMass runtime ks ep msg

/-- Correctness for every generated key, message and epoch satisfying the supplied predicate.
Returned failure, rejection and missing mass count against the error allowance. -/
@[expose] def CompleteOnPerKey (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (active : E → Prop) (δ : ℝ≥0∞) : Prop :=
  ∀ ks, alg.Generated runtime ks → ∀ ep, active ep → ∀ msg,
    1 - δ ≤ alg.successMass runtime ks ep msg

/-- Restricting to every epoch is the usual per-key correctness property. -/
theorem completeOnPerKey_true_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) :
    alg.CompleteOnPerKey runtime (fun _ => True) δ ↔ alg.CompletePerKey runtime δ := by
  simp only [CompleteOnPerKey, CompletePerKey, forall_const]


/-- The fully quantified per-key characterization of correctness. -/
theorem completePerKey_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) :
    alg.CompletePerKey runtime δ ↔ ∀ ks,
      0 < runtime.evalDist ((fun ks' => ks' = ks) <$> alg.keygen) {True} → ∀ ep msg,
      1 - δ ≤ runtime.evalDist
        (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) {true} := by
  simp only [CompletePerKey, Generated, successMass_eq_probability]

/-- Increasing the permitted error preserves correctness. -/
theorem CompletePerKey.mono {alg : SyncSignatureAlg m M PK SK S E}
    {runtime : ProbCompRuntime m} {δ₁ δ₂ : ℝ≥0∞}
    (h : alg.CompletePerKey runtime δ₁) (hle : δ₁ ≤ δ₂) : alg.CompletePerKey runtime δ₂ :=
  fun ks hks ep msg => (tsub_le_tsub_left hle 1).trans (h ks hks ep msg)

/-- Zero error is exactly unit success mass at every producible key, epoch and message. -/
theorem completePerKey_zero_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) :
    alg.CompletePerKey runtime 0 ↔ ∀ ks, alg.Generated runtime ks → ∀ ep msg,
      alg.successMass runtime ks ep msg = 1 := by
  constructor
  · intro h ks hks ep msg
    exact le_antisymm (alg.successMass_le_one runtime ks ep msg)
      (by simpa using h ks hks ep msg)
  · intro h ks hks ep msg
    simpa using le_of_eq (h ks hks ep msg).symm

/-- The joint key-generation, signing and deterministic-verification experiment.
Returned `none` is rejected; native execution failure remains missing mass. -/
@[expose] def correctnessExperiment (alg : SyncSignatureAlg m M PK SK S E)
    (ep : E) (msg : M) : m Bool := do
  let (pk, sk) ← alg.keygen
  alg.accepts pk ep msg <$> alg.sign sk ep msg

/-- Successful verification mass in the joint key-generation/signing experiment. -/
@[expose] noncomputable def jointSuccessMass (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ep : E) (msg : M) : ℝ≥0∞ :=
  runtime.evalDist (alg.correctnessExperiment ep msg) {true}

/-- Joint correctness at every epoch and message, without conditioning on successful execution. -/
@[expose] def Complete (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) : Prop :=
  ∀ ep msg, 1 - δ ≤ alg.jointSuccessMass runtime ep msg

/-- Joint correctness at each active epoch and every message. -/
@[expose] def CompleteOn (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (active : E → Prop) (δ : ℝ≥0∞) : Prop :=
  ∀ ep, active ep → ∀ msg, 1 - δ ≤ alg.jointSuccessMass runtime ep msg

end SyncSignatureAlg
