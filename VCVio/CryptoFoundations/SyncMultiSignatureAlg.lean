/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.IndepProduct

/-!
# Synchronized multi-signature algorithms, correctness, and security

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

`SyncMultiSignatureUnforgeability` defines adaptive regular unforgeability with one challenger
key and an adversary-supplied ordered tuple of public keys and aggregate signature.
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

/-!
## Synchronized multi-signature unforgeability

Definition 10 of ePrint 2025/055, printed page 13, uses one challenger key and a classical
adaptive signing oracle. The adversary supplies an ordered tuple of arbitrary public keys and
an aggregate signature directly. Verification, first-message freshness at the forged epoch,
and challenger-key membership are exactly the winning conditions. No registration, distinctness,
proof of possession, individual verification or honest generation of other keys is imposed.

The richer first-request history from synchronized signatures is reused through `messageHistory`.
A returned signing failure consumes its epoch and permits continuation; divergence remains
missing execution mass. Validity is checked after runtime interpretation, without normalization.
The ambient specification is public to algorithms and adversary; `unifSpec` supplies probabilistic
sampling without imposing a random-oracle model. Efficiency restrictions belong to explicit
admissible adversary classes when applying bounds, separately from this semantic interaction.
-/

namespace SyncMultiSignatureUnforgeability

open OracleSpec OracleComp ENNReal
open SyncSignatureUnforgeability (History emptyHistory signingSpec)

universe u

variable {M PK SK S A E : Type}

/-- An adversary-chosen ordered participant tuple, epoch, message and aggregate signature. -/
structure Forgery (PK E M A : Type) where
  /-- The participant arity may be zero. -/
  arity : ℕ
  /-- Public keys retain their order and multiplicity. -/
  pks : Fin arity → PK
  /-- The candidate's synchronized epoch. -/
  ep : E
  /-- The candidate's common message. -/
  msg : M
  /-- The aggregate is supplied directly, without individual signatures. -/
  signature : A

/-- The paper's message-only `Signed` state projects the first eligible request. -/
@[expose] def messageHistory (history : History E M S) (ep : E) : Option M :=
  (history ep).map Prod.fst

/-- The forged message must differ from the first eligible message at its own epoch. -/
@[expose] def fresh [DecidableEq M] (history : History E M S) (ep : E) (msg : M) : Bool :=
  decide (messageHistory history ep ≠ some msg)

/-- An unused epoch makes every message fresh. -/
theorem fresh_unused [DecidableEq M] (history : History E M S) (ep : E) (msg : M)
    (h : history ep = none) : fresh history ep msg = true := by
  simp [fresh, messageHistory, h]

/-- Both successful and failed first requests exclude exactly their message. -/
theorem fresh_used [DecidableEq M] (history : History E M S) (ep : E)
    (msg first : M) (answer : Option S) (h : history ep = some (first, answer)) :
    fresh history ep msg = decide (msg ≠ first) := by
  simp [fresh, messageHistory, h, ne_comm]

/-- The projection after an eligible request records its message independently of the answer. -/
theorem messageHistory_record_unused [DecidableEq E] (history : History E M S)
    (ep : E) (msg : M) (answer : Option S) (h : history ep = none) :
    messageHistory (SyncSignatureUnforgeability.record history ep msg answer) ep = some msg := by
  simp [messageHistory, SyncSignatureUnforgeability.record_unused history ep msg answer h]

/-- At least one index must carry the challenger key; other keys are unrestricted. -/
@[expose] def containsKey [DecidableEq PK] {k : ℕ} (pks : Fin k → PK) (pk : PK) : Bool :=
  decide (∃ i, pks i = pk)

/-- Membership is exactly existential equality at an index in the original tuple. -/
theorem containsKey_iff [DecidableEq PK] {k : ℕ} (pks : Fin k → PK) (pk : PK) :
    containsKey pks pk = true ↔ ∃ i, pks i = pk := by
  simp [containsKey]

/-- The empty participant tuple never includes the challenger key. -/
theorem containsKey_empty [DecidableEq PK] (pks : Fin 0 → PK) (pk : PK) :
    containsKey pks pk = false := by
  simp [containsKey]

/-- A singleton contains the challenger key precisely when its entry equals that key. -/
theorem containsKey_singleton [DecidableEq PK] (other pk : PK) :
    containsKey (fun _ : Fin 1 => other) pk = decide (other = pk) := by
  simp [containsKey]

/-- The challenger key, candidate and final history contain all data needed for validity. -/
@[expose] def ExperimentResult (PK E M S A : Type) :=
  PK × Forgery PK E M A × History E M S

variable {ι : Type u} {spec : OracleSpec ι}

/-- A classical adaptive Definition 10 EUF-CMA adversary receives one challenger key and the
public oracle interface. -/
structure Adversary (spec : OracleSpec ι) (PK E M S A : Type) where
  /-- Choose a candidate after arbitrary adaptive ambient and individual-signing queries. -/
  forge : PK → OracleComp (spec + signingSpec E M S) (Forgery PK E M A)

/-- Reject consumed epochs before invoking signing, retaining the entire first-request record. -/
@[expose] def signingOracle [DecidableEq E]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E) (sk : SK) :
    QueryImpl (signingSpec E M S) (StateT (History E M S) (OracleComp spec)) :=
  fun ⟨ep, msg⟩ history =>
    match history ep with
    | some _ => pure (none, history)
    | none => do
      let answer ← alg.sign sk ep msg
      pure (answer, Function.update history ep (some (msg, answer)))

/-- A duplicate returns failure and the unchanged history, without executing the signer. -/
theorem signingOracle_used [DecidableEq E]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E) (sk : SK)
    (history : History E M S) (ep : E) (msg first : M) (answer : Option S)
    (h : history ep = some (first, answer)) :
    signingOracle alg sk (ep, msg) history = pure (none, history) := by
  simp [signingOracle, h]

/-- An eligible request invokes signing and records the first message even on returned failure. -/
theorem signingOracle_unused [DecidableEq E]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E) (sk : SK)
    (history : History E M S) (ep : E) (msg : M) (h : history ep = none) :
    signingOracle alg sk (ep, msg) history = (do
      let answer ← alg.sign sk ep msg
      pure (answer, Function.update history ep (some (msg, answer)))) := by
  simp [signingOracle, h]

/-- Generate one challenger key and run the adversary with secret-key signing access only. -/
@[expose] def interaction [DecidableEq E]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (adv : Adversary spec PK E M S A) : OracleComp spec (ExperimentResult PK E M S A) := do
  let (pk, sk) ← alg.keygen
  let impl : QueryImpl (spec + signingSpec E M S)
      (StateT (History E M S) (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
      (StateT (History E M S) (OracleComp spec)) + signingOracle alg sk
  let (forgery, history) ← (simulateQ impl (adv.forge pk)).run emptyHistory
  pure (pk, forgery, history)

/-- Verify the original tuple and aggregate, require message freshness and challenger membership. -/
@[expose] def valid [DecidableEq M] [DecidableEq PK]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (out : ExperimentResult PK E M S A) : Bool :=
  let result := out.2
  let forgery := result.1
  alg.verify forgery.pks forgery.ep forgery.msg forgery.signature &&
    fresh result.2 forgery.ep forgery.msg && containsKey forgery.pks out.1

/-- Definition 10 validity has exactly its three independently necessary conditions. -/
theorem valid_iff [DecidableEq M] [DecidableEq PK]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (out : ExperimentResult PK E M S A) :
    let result := out.2
    let forgery := result.1
    valid alg out = true ↔
      alg.verify forgery.pks forgery.ep forgery.msg forgery.signature = true ∧
      messageHistory result.2 forgery.ep ≠ some forgery.msg ∧
      ∃ i, forgery.pks i = out.1 := by
  simp [valid, fresh, containsKey, and_assoc]

/-- The Boolean measure obtained by checking a winning condition on the common interaction result.
Both Boolean outcomes retain their original mass; missing execution mass is not normalized. -/
@[expose] noncomputable def outputMeasure [DecidableEq E]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S A)
    (winCondition : ExperimentResult PK E M S A → Bool) :
    MeasureTheory.Measure Bool :=
  runtime.evalDist (winCondition <$> interaction alg adv)

/-- Definition 10 regular multi-signature EUF-CMA as a Boolean winning measure.
The winning observation follows runtime interpretation and retains missing execution mass. -/
@[expose] noncomputable def unforgeableExp [DecidableEq E] [DecidableEq M] [DecidableEq PK]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S A) :
    MeasureTheory.Measure Bool :=
  outputMeasure alg runtime adv (valid alg)

/-- The public experiment is exactly the post-runtime winning measure. -/
theorem unforgeableExp_eq_outputMeasure [DecidableEq E] [DecidableEq M] [DecidableEq PK]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S A) :
    unforgeableExp alg runtime adv = outputMeasure alg runtime adv (valid alg) := rfl

/-- Unforgeability advantage is the unnormalized winning mass after runtime interpretation. -/
@[expose] noncomputable def advantage [DecidableEq E] [DecidableEq M] [DecidableEq PK]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S A) : ℝ≥0∞ :=
  unforgeableExp alg runtime adv {true}

/-- The public measure agrees with the unnormalized probability of the checked Boolean output. -/
theorem outputMeasure_apply_singleton [DecidableEq E]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S A)
    (winCondition : ExperimentResult PK E M S A → Bool) (b : Bool) :
    outputMeasure alg runtime adv winCondition {b} =
      runtime.evalDist (winCondition <$> interaction alg adv) {b} := rfl

/-- Checking the interaction produces a subprobability measure, preserving missing mass. -/
theorem outputMeasure_mass_le_one [DecidableEq E]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S A)
    (winCondition : ExperimentResult PK E M S A → Bool) :
    outputMeasure alg runtime adv winCondition Set.univ ≤ 1 :=
  runtime.evalDist_apply_univ_le_one _

/-- Entirely missing runtime transcript mass produces zero winning probability. -/
theorem outputMeasure_eq_zero_of_failure [DecidableEq E]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S A)
    (winCondition : ExperimentResult PK E M S A → Bool)
    (h : runtime.evalDist (winCondition <$> interaction alg adv) = 0) :
    outputMeasure alg runtime adv winCondition {true} = 0 := by
  simp [outputMeasure, h]

/-- The output measure is the native runtime observation of the checked surface program. -/
theorem outputMeasure_eq_runtime [DecidableEq E]
    (alg : SyncMultiSignatureAlg (OracleComp spec) M PK SK S A E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S A)
    (winCondition : ExperimentResult PK E M S A → Bool) :
    outputMeasure alg runtime adv winCondition {true} =
      runtime.evalDist (winCondition <$> interaction alg adv) {true} := rfl

end SyncMultiSignatureUnforgeability
