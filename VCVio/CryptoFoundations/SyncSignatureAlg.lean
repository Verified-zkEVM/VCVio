/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.OracleComp.ProbCompLift
public import VCVio.EvalDist.Defs.Instances
public import VCVio.EvalDist.Defs.Measure

/-!
# Synchronized signature algorithms and per-key correctness

Epoch-indexed algorithms specialize to ePrint 2025/055, Definition 7 (page 12), with
`E := Fin L`. A concrete scheme constructor fixes its system configuration for all three
algorithms. Correctness for a family `scheme` is expressed by
`∀ cfg, (scheme cfg).Complete runtime (errorBound cfg)`. The THF parameter sampled by GXMSS
key generation remains distinct key material. Message types can be instantiated with fixed-length
bit strings. Efficiency is not modeled.

The interface assumes no equality decision, ordering or finiteness of `E`. Consumers that
compare or enumerate epochs supply those structures where needed; concrete GXMSS uses
`Fin (2 ^ h)` for tree height `h`.

Correctness observes signing in the supplied runtime, then maps `none` to `false` and a returned
signature to deterministic verification. This preserves missing mass without a normalization.
The runtime need not commute with this map. `successMass_eq_runtime` explicitly assumes the
factoring equation when a caller wants to move the observation into the surface computation.
Producibility means positive point mass in this same runtime, not structural oracle support.
The paper's total key generator additionally requires losslessness of the chosen keygen semantics;
the per-produced-key correctness predicate itself makes no keygen termination claim.
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
  0 < Pr[= ks | runtime.evalSPMF alg.keygen]

/-- Runtime-positive producibility is exactly membership in its SPMF support. -/
theorem generated_iff_mem_support (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) :
    alg.Generated runtime ks ↔ ks ∈ (runtime.evalSPMF alg.keygen).support := by
  exact probOutput_pos_iff (mx := runtime.evalSPMF alg.keygen) (x := ks)

/-- The successful-output measure of verification observations, preserving missing signing mass. -/
@[expose] noncomputable def verificationDist (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) :
    MeasureTheory.Measure Bool :=
  𝒟[alg.accepts ks.1 ep msg <$> runtime.evalSPMF (alg.sign ks.2 ep msg)]

/-- The unnormalized probability of successful verification for a fixed key pair. -/
@[expose] noncomputable def successMass (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) : ℝ≥0∞ :=
  alg.verificationDist runtime ks ep msg {true}

/-- The measure singleton agrees with the runtime's discrete successful-output probability. -/
theorem successMass_eq_probability (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) :
    alg.successMass runtime ks ep msg = Pr[= true | alg.accepts ks.1 ep msg <$>
      runtime.evalSPMF (alg.sign ks.2 ep msg)] := by
  simp [successMass, verificationDist]

/-- Successful verification has subprobability mass at most one. -/
theorem successMass_le_one (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) :
    alg.successMass runtime ks ep msg ≤ 1 := by
  rw [successMass_eq_probability]
  exact probOutput_le_one

/-- A signer observed as returned `none` has no successful verification mass. -/
theorem successMass_eq_zero_of_none (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M)
    (h : runtime.evalSPMF (alg.sign ks.2 ep msg) = pure none) :
    alg.successMass runtime ks ep msg = 0 := by
  simp [successMass, verificationDist, h]

/-- A signer with entirely missing output mass has no successful verification mass. -/
theorem successMass_eq_zero_of_failure (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M)
    (h : runtime.evalSPMF (alg.sign ks.2 ep msg) = failure) :
    alg.successMass runtime ks ep msg = 0 := by
  simp [successMass, verificationDist, h]

/-- The success probability is the measure of the measurable singleton `{true}` on `Bool`. -/
theorem successMass_eq_measure (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) :
    alg.successMass runtime ks ep msg =
      alg.verificationDist runtime ks ep msg {true} := rfl

/-- Transport into the surface program requires exactly the stated runtime factoring law. -/
theorem successMass_eq_runtime (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M)
    (hfactor : runtime.evalSPMF (alg.sign ks.2 ep msg >>= fun sig =>
      pure (alg.accepts ks.1 ep msg sig)) =
      alg.accepts ks.1 ep msg <$> runtime.evalSPMF (alg.sign ks.2 ep msg)) :
    alg.successMass runtime ks ep msg = Pr[= true | runtime.evalSPMF
      (alg.sign ks.2 ep msg >>= fun sig => pure (alg.accepts ks.1 ep msg sig))] := by
  rw [successMass_eq_probability, hfactor]

/-- Correctness for every producible key pair, epoch and message of this scheme instance.
Returned failure, verification rejection and missing mass all count against `δ`. -/
@[expose] def Complete (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) : Prop :=
  ∀ ks, alg.Generated runtime ks → ∀ ep msg,
    1 - δ ≤ alg.successMass runtime ks ep msg

/-- The fully quantified per-key characterization of correctness. -/
theorem complete_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) :
    alg.Complete runtime δ ↔ ∀ ks,
      0 < Pr[= ks | runtime.evalSPMF alg.keygen] → ∀ ep msg,
      1 - δ ≤ Pr[= true | alg.accepts ks.1 ep msg <$>
        runtime.evalSPMF (alg.sign ks.2 ep msg)] := by
  simp only [Complete, Generated, successMass_eq_probability]

/-- Increasing the permitted error preserves correctness. -/
theorem Complete.mono {alg : SyncSignatureAlg m M PK SK S E}
    {runtime : ProbCompRuntime m} {δ₁ δ₂ : ℝ≥0∞}
    (h : alg.Complete runtime δ₁) (hle : δ₁ ≤ δ₂) : alg.Complete runtime δ₂ :=
  fun ks hks ep msg => (tsub_le_tsub_left hle 1).trans (h ks hks ep msg)

/-- Zero error is exactly unit success mass at every producible key, epoch and message. -/
theorem complete_zero_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) :
    alg.Complete runtime 0 ↔ ∀ ks, alg.Generated runtime ks → ∀ ep msg,
      alg.successMass runtime ks ep msg = 1 := by
  simp [Complete, successMass_eq_probability]

end SyncSignatureAlg

