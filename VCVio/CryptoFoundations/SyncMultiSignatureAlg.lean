/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.IndepProduct

/-!
# Synchronized multi-signature algorithms and correctness

Definition 9 of ePrint 2025/055, printed page 13, with fixed configuration captured by the
scheme constructor and abstract epochs (the paper specializes to `Fin L`). The individual and
aggregate signature spaces are separate. Finite indexed pairs preserve alignment, including
empty tuples and repeated keys; neither ordering invariance nor an individual verifier is required.

The reference experiment independently samples each signer's runtime interpretation, then observes
all returned signatures by deterministic aggregation and verification. Returned `none` is rejected;
missing mass stays missing and also counts against correctness. The bound ranges over every tuple
of individually runtime-producible keys and is indexed by its participant count. Efficiency and
lossless key generation are separate paper-instantiation obligations.

The native observation is taken over the surface computation itself. `Fin.mOfFn` therefore
retains fresh, ordered coordinate sampling, including empty and repeated-key tuples, while the
runtime measure retains returned failure and missing mass.
-/

public section


open ENNReal

universe v

/-- Four synchronized multi-signature algorithms at fixed constructor configuration. -/
structure SyncMultiSignatureAlg (m : Type → Type v) [Monad m]
    (M PK SK S A E : Type) where
  /-- Generate a public and secret key for this scheme instance. -/
  keygen : m (PK × SK)
  /-- Sign the shared message and epoch, possibly returning explicit failure. -/
  sign : SK → E → M → m (Option S)
  /-- Aggregate an aligned tuple of public keys and successful individual signatures. -/
  aggregate : {k : ℕ} → E → M → (Fin k → PK × S) → A
  /-- Verify against the corresponding ordered public-key tuple. -/
  verify : {k : ℕ} → (Fin k → PK) → E → M → A → Bool

namespace SyncMultiSignatureAlg

variable {m : Type → Type v} [Monad m] {M PK SK S A E : Type}

/-- A key pair is producible when its point mass in the selected runtime is positive. -/
@[expose] def Generated (alg : SyncMultiSignatureAlg m M PK SK S A E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) : Prop :=
  0 < runtime.evalDist ((fun ks' => ks' = ks) <$> alg.keygen) {True}

/-- Every coordinate is individually producible, with no distinctness restriction. -/
@[expose] def GeneratedTuple (alg : SyncMultiSignatureAlg m M PK SK S A E)
    (runtime : ProbCompRuntime m) {k : ℕ} (keys : Fin k → PK × SK) : Prop :=
  ∀ i, alg.Generated runtime (keys i)

/-- Observe optional signing outputs; any returned failure rejects the aggregate. -/
@[expose] def accepts (alg : SyncMultiSignatureAlg m M PK SK S A E)
    {k : ℕ} (pks : Fin k → PK) (ep : E) (msg : M) (outs : Fin k → Option S) : Bool :=
  match Fin.mOfFn k outs with
  | none => false
  | some sigs => alg.verify pks ep msg (alg.aggregate ep msg fun i => (pks i, sigs i))

/-- Unnormalized success mass for a fixed tuple, epoch and message. -/
@[expose] noncomputable def successMass
    (alg : SyncMultiSignatureAlg m M PK SK S A E) (runtime : ProbCompRuntime m)
    {k : ℕ} (keys : Fin k → PK × SK) (ep : E) (msg : M) : ℝ≥0∞ :=
  runtime.evalDist (alg.accepts (fun i => (keys i).1) ep msg <$>
    Fin.mOfFn k (fun i => alg.sign (keys i).2 ep msg)) {true}

/-- The aggregate observation's measure agrees with its discrete probability. -/
theorem successMass_eq_probability (alg : SyncMultiSignatureAlg m M PK SK S A E)
    (runtime : ProbCompRuntime m) {k : ℕ} (keys : Fin k → PK × SK) (ep : E) (msg : M) :
    alg.successMass runtime keys ep msg = runtime.evalDist
      (alg.accepts (fun i => (keys i).1) ep msg <$>
        Fin.mOfFn k (fun i => alg.sign (keys i).2 ep msg)) {true} := rfl

/-- Fresh ordered signing coordinates have the product of their singleton-event masses.
This includes empty tuples and repeated keys, and retains every coordinate's missing mass. -/
theorem independent_signing_probability [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m] (alg : SyncMultiSignatureAlg m M PK SK S A E)
    {k : ℕ} (keys : Fin k → PK × SK) (ep : E) (msg : M)
    (outs : Fin k → Option S) :
    Pr{let sampled ← Fin.mOfFn k (fun i => alg.sign (keys i).2 ep msg)}[
      sampled = outs] =
      ∏ i, Pr{let out ← alg.sign (keys i).2 ep msg}[out = outs i] :=
  prEvent_eq_mOfFn k _ outs

/-- Aggregate success has at most unit mass. -/
theorem successMass_le_one (alg : SyncMultiSignatureAlg m M PK SK S A E)
    (runtime : ProbCompRuntime m) {k : ℕ} (keys : Fin k → PK × SK) (ep : E) (msg : M) :
    alg.successMass runtime keys ep msg ≤ 1 := by
  rw [successMass_eq_probability]
  exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans
    (runtime.evalDist_apply_univ_le_one _)

/-- Definition 9 correctness at every participant count and individually producible key tuple.
All rejection, returned failure and missing computation mass counts against `δ k`. -/
@[expose] def Complete (alg : SyncMultiSignatureAlg m M PK SK S A E)
    (runtime : ProbCompRuntime m) (δ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (k : ℕ) (keys : Fin k → PK × SK), alg.GeneratedTuple runtime keys → ∀ ep msg,
    1 - δ k ≤ alg.successMass runtime keys ep msg

/-- The fully expanded quantifiers and independent signing observation in correctness. -/
theorem complete_iff (alg : SyncMultiSignatureAlg m M PK SK S A E)
    (runtime : ProbCompRuntime m) (δ : ℕ → ℝ≥0∞) :
    alg.Complete runtime δ ↔ ∀ (k : ℕ) (keys : Fin k → PK × SK),
      (∀ i, 0 < runtime.evalDist ((fun ks' => ks' = keys i) <$> alg.keygen) {True}) →
      ∀ ep msg, 1 - δ k ≤ runtime.evalDist
        (alg.accepts (fun i => (keys i).1) ep msg <$>
          Fin.mOfFn k (fun i => alg.sign (keys i).2 ep msg)) {true} := by
  simp only [Complete, GeneratedTuple, Generated, successMass_eq_probability]

/-- Increasing any participant-count error allowance preserves correctness. -/
theorem Complete.mono {alg : SyncMultiSignatureAlg m M PK SK S A E}
    {runtime : ProbCompRuntime m} {δ₁ δ₂ : ℕ → ℝ≥0∞}
    (h : alg.Complete runtime δ₁) (hle : ∀ k, δ₁ k ≤ δ₂ k) :
    alg.Complete runtime δ₂ :=
  fun k keys hkeys ep msg => (tsub_le_tsub_left (hle k) 1).trans (h k keys hkeys ep msg)

/-- Empty tuples satisfy the producibility condition even if key generation has no output. -/
theorem generatedTuple_empty (alg : SyncMultiSignatureAlg m M PK SK S A E)
    (runtime : ProbCompRuntime m) (keys : Fin 0 → PK × SK) :
    alg.GeneratedTuple runtime keys := fun i => i.elim0

/-- Empty aggregation is still verified, rather than being assumed to succeed. -/
theorem accepts_empty (alg : SyncMultiSignatureAlg m M PK SK S A E)
    (pks : Fin 0 → PK) (ep : E) (msg : M) (outs : Fin 0 → Option S) :
    alg.accepts pks ep msg outs =
      alg.verify pks ep msg (alg.aggregate ep msg fun i => (pks i, i.elim0)) := rfl

end SyncMultiSignatureAlg
