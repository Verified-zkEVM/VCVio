/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.SymmEncAlg.Measure
public import VCVio.CryptoFoundations.SymmEncAlg.OneTimeINDCPA
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.OracleComp.SimSemantics.Append.Core

/-!
# Deterministic symmetric encryption and IND$-CPA

A deterministic symmetric encryption scheme `DetSymmEncAlg M K C` has probabilistic key generation
and pure encryption and decryption. It embeds into the monadic `SymmEncAlg ProbComp M K C` through
`DetSymmEncAlg.toSymmEncAlg`.

The security notion is IND$-CPA (Rogaway 2004; Namprempre, Rogaway and Shrimpton 2014): an
adversary with oracle access to uniform sampling and an encryption oracle `M →ₒ C` cannot tell
whether the oracle answers `encrypt k msg` under a hidden key or a fresh uniform ciphertext.

## Allowed adversaries

The game places no restriction on the adversary. A deterministic scheme cannot be IND$-CPA
secure against adversaries that repeat an encryption query: the real oracle answers a repeated
query identically, while the ideal oracle answers it independently. Security of a deterministic
scheme is therefore claimed only for adversaries whose encryption queries are pairwise distinct.
For a nonce-based scheme presented with message space `N × M'`, this includes the nonce-respecting
adversaries of Namprempre, Rogaway and Shrimpton. Theorems that assume IND$-CPA security state the
query restriction as a hypothesis, for example a one-query bound
`IsQueryBoundP adversary IsEncQuery 1`, rather than building it into the game.

The ideal oracle samples from the fixed type `C`. Schemes whose ciphertext length depends on the
message are modelled by instantiating `C` per length.

## Main results

* `DetSymmEncAlg.measureComplete_toSymmEncAlg`: pointwise correctness gives measure-level
  completeness of the induced monadic scheme.
* `DetSymmEncAlg.IND_CPA_OneTime_Advantage_eq_two_mul_indDollarAdvantage`: the one-time
  IND-CPA advantage of the induced scheme is exactly twice the IND$-CPA advantage of the
  one-query reduction `DetSymmEncAlg.oneTimeINDCPAReduction`.

## References

* P. Rogaway, *Nonce-based symmetric encryption*, FSE 2004.
* C. Namprempre, P. Rogaway, T. Shrimpton, *Reconsidering generic composition*,
  EUROCRYPT 2014.
-/

public section

open MeasureTheory OracleComp OracleSpec ENNReal

/-- A deterministic symmetric encryption scheme with message space `M`, key space `K`, and
ciphertext space `C`: key generation is probabilistic, while encryption and decryption are pure
functions of the key. -/
structure DetSymmEncAlg (M K C : Type) where
  /-- Sample a key. -/
  keygen : ProbComp K
  /-- Encrypt a message under a key. -/
  encrypt : K → M → C
  /-- Decrypt a ciphertext under a key, returning `none` on failure. -/
  decrypt : K → C → Option M

namespace DetSymmEncAlg

variable {M K C : Type}

/-! ## Embedding and correctness -/

/-- The monadic symmetric encryption scheme whose encryption and decryption return the
deterministic results. -/
@[expose]
def toSymmEncAlg (scheme : DetSymmEncAlg M K C) : SymmEncAlg ProbComp M K C where
  keygen := scheme.keygen
  encrypt k msg := pure (scheme.encrypt k msg)
  decrypt k c := pure (scheme.decrypt k c)

@[simp]
lemma toSymmEncAlg_keygen (scheme : DetSymmEncAlg M K C) :
    scheme.toSymmEncAlg.keygen = scheme.keygen := rfl

@[simp]
lemma toSymmEncAlg_encrypt (scheme : DetSymmEncAlg M K C) (k : K) (msg : M) :
    scheme.toSymmEncAlg.encrypt k msg = pure (scheme.encrypt k msg) := rfl

@[simp]
lemma toSymmEncAlg_decrypt (scheme : DetSymmEncAlg M K C) (k : K) (c : C) :
    scheme.toSymmEncAlg.decrypt k c = pure (scheme.decrypt k c) := rfl

/-- Perfect correctness: under every key, decryption inverts encryption. -/
def PerfectlyCorrect (scheme : DetSymmEncAlg M K C) : Prop :=
  ∀ (k : K) (msg : M), scheme.decrypt k (scheme.encrypt k msg) = some msg

/-- Pointwise correctness of a deterministic scheme gives measure-level completeness of the induced
monadic scheme: every round trip has the Dirac law at the input message. -/
theorem measureComplete_toSymmEncAlg [MeasurableSpace M] (scheme : DetSymmEncAlg M K C)
    (hcorrect : scheme.PerfectlyCorrect) :
    scheme.toSymmEncAlg.measureComplete ProbabilitySemantics.freeM := by
  intro msg
  have hprogram : scheme.toSymmEncAlg.completenessExperiment msg =
      (fun _ : K ↦ some msg) <$> scheme.keygen := by
    simp [SymmEncAlg.completenessExperiment, hcorrect _ msg, map_eq_bind_pure_comp]
  rw [hprogram]
  change 𝒟[(fun _ : K ↦ some msg) <$> scheme.keygen] = _
  let : MeasurableSpace K := ⊤
  rw [evalDist_map scheme.keygen measurable_const, Measure.map_const]
  simp

/-! ## IND$-CPA -/

/-- Oracle interface of an IND$-CPA adversary: uniform sampling plus an encryption oracle. -/
@[expose, reducible] def INDDollarOracleSpec (M C : Type) := unifSpec + (M →ₒ C)

/-- An IND$-CPA adversary: an oracle computation with access to uniform sampling and an encryption
oracle, returning a guess (`true` for the real encryption oracle). -/
abbrev INDDollarAdversary (M C : Type) := OracleComp (INDDollarOracleSpec M C) Bool

/-- Query the encryption oracle of the IND$-CPA interface. -/
@[expose] def encQuery (msg : M) : OracleComp (INDDollarOracleSpec M C) C :=
  (INDDollarOracleSpec M C).query (Sum.inr msg)

/-- The encryption-oracle indices of the IND$-CPA interface `INDDollarOracleSpec M C`, used to
bound encryption queries with `IsQueryBoundP`. -/
@[expose] def IsEncQuery (t : ℕ ⊕ M) : Prop := t.isRight = true

instance : DecidablePred (IsEncQuery (M := M)) :=
  fun t ↦ inferInstanceAs (Decidable (t.isRight = true))

/-- Real IND$-CPA oracle: uniform-sampling queries are forwarded and encryption queries are
answered by `scheme.encrypt k`. -/
@[expose]
def indDollarRealQueryImpl (scheme : DetSymmEncAlg M K C) (k : K) :
    QueryImpl (INDDollarOracleSpec M C) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    (fun msg ↦ pure (scheme.encrypt k msg) : QueryImpl (M →ₒ C) ProbComp)

/-- Ideal IND$-CPA oracle: uniform-sampling queries are forwarded and every encryption query is
answered by a fresh uniform ciphertext, independently of the message and of earlier answers. -/
@[expose]
def indDollarIdealQueryImpl [SampleableType C] :
    QueryImpl (INDDollarOracleSpec M C) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    (fun _ ↦ $ᵗ C : QueryImpl (M →ₒ C) ProbComp)

/-- Real IND$-CPA experiment: sample a key and run the adversary against the real oracle. -/
@[expose]
def indDollarRealExperiment (scheme : DetSymmEncAlg M K C) (adversary : INDDollarAdversary M C) :
    ProbComp Bool := do
  let k ← scheme.keygen
  simulateQ (scheme.indDollarRealQueryImpl k) adversary

/-- Ideal IND$-CPA experiment: run the adversary against the random-ciphertext oracle. -/
@[expose]
def indDollarIdealExperiment [SampleableType C] (adversary : INDDollarAdversary M C) :
    ProbComp Bool :=
  simulateQ (indDollarIdealQueryImpl (M := M) (C := C)) adversary

/-- IND$-CPA advantage: the distinguishing advantage `Measure.boolDist` between the real and
ideal experiments. -/
@[expose]
noncomputable def indDollarAdvantage [SampleableType C] (scheme : DetSymmEncAlg M K C)
    (adversary : INDDollarAdversary M C) : ℝ≥0∞ :=
  𝒟[scheme.indDollarRealExperiment adversary].boolDist 𝒟[indDollarIdealExperiment adversary]

/-! ## Forwarding lemmas for the IND$-CPA oracles

Both oracles are transparent on computations lifted from `ProbComp`, and an encryption query is
answered by `pure (scheme.encrypt k msg)` in the real world and by `$ᵗ C` in the ideal world. -/

/-- The real IND$-CPA oracle is transparent on a computation lifted from `ProbComp`. -/
@[simp]
lemma simulateQ_indDollarRealQueryImpl_liftM (scheme : DetSymmEncAlg M K C) (k : K)
    {α : Type} (oa : ProbComp α) :
    simulateQ (scheme.indDollarRealQueryImpl k)
      (liftM oa : OracleComp (INDDollarOracleSpec M C) α) = oa := by
  simp [indDollarRealQueryImpl, QueryImpl.simulateQ_add_liftM_left,
    QueryImpl.simulateQ_toQueryImpl]

/-- The ideal IND$-CPA oracle is transparent on a computation lifted from `ProbComp`. -/
@[simp]
lemma simulateQ_indDollarIdealQueryImpl_liftM [SampleableType C] {α : Type} (oa : ProbComp α) :
    simulateQ (indDollarIdealQueryImpl (M := M) (C := C))
      (liftM oa : OracleComp (INDDollarOracleSpec M C) α) = oa := by
  simp [indDollarIdealQueryImpl, QueryImpl.simulateQ_add_liftM_left,
    QueryImpl.simulateQ_toQueryImpl]

/-- The real IND$-CPA oracle answers an encryption query by encrypting under the hidden key. -/
@[simp]
lemma simulateQ_indDollarRealQueryImpl_encQuery (scheme : DetSymmEncAlg M K C) (k : K) (msg : M) :
    simulateQ (scheme.indDollarRealQueryImpl k) (encQuery msg) = pure (scheme.encrypt k msg) := by
  simp [indDollarRealQueryImpl, encQuery]

/-- The ideal IND$-CPA oracle answers an encryption query by a fresh uniform ciphertext. -/
@[simp]
lemma simulateQ_indDollarIdealQueryImpl_encQuery [SampleableType C] (msg : M) :
    simulateQ (indDollarIdealQueryImpl (M := M) (C := C)) (encQuery msg) = $ᵗ C := by
  simp [indDollarIdealQueryImpl, encQuery]

/-! ## One-time IND-CPA from IND$-CPA -/

/-- The IND$-CPA adversary built from a one-time IND-CPA adversary: sample the hidden bit, let
the adversary choose two messages, submit the selected message as the single encryption query,
and report whether the adversary recovers the bit. -/
@[expose]
def oneTimeINDCPAReduction (scheme : DetSymmEncAlg M K C)
    (adv : scheme.toSymmEncAlg.IND_CPA_OneTime_Adversary) : INDDollarAdversary M C :=
  (do
    let b ← liftComp ($ᵗ Bool) (INDDollarOracleSpec M C)
    let msgs ← liftComp adv.chooseMessages (INDDollarOracleSpec M C)
    let c ← encQuery (if b then msgs.1 else msgs.2.1)
    let b' ← liftComp (adv.distinguish msgs.2.2 c) (INDDollarOracleSpec M C)
    pure (b == b') : OracleComp (INDDollarOracleSpec M C) Bool)

/-- A computation lifted from `ProbComp` makes no encryption queries. -/
lemma isQueryBoundP_liftComp_isEncQuery {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftComp oa (INDDollarOracleSpec M C)) IsEncQuery 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
      rw [liftComp_bind, liftComp_query]
      change IsQueryBoundP (liftM ((INDDollarOracleSpec M C).query (Sum.inl t)) >>=
        fun u ↦ liftComp (mx u) (INDDollarOracleSpec M C)) IsEncQuery 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨by simp [IsEncQuery], fun u ↦ by simpa [IsEncQuery] using ih u⟩

/-- The reduction makes at most one encryption query. -/
theorem isQueryBoundP_oneTimeINDCPAReduction (scheme : DetSymmEncAlg M K C)
    (adv : scheme.toSymmEncAlg.IND_CPA_OneTime_Adversary) :
    IsQueryBoundP (scheme.oneTimeINDCPAReduction adv) IsEncQuery 1 := by
  unfold oneTimeINDCPAReduction
  refine (isQueryBoundP_bind (n := 0) (m := 1) (isQueryBoundP_liftComp_isEncQuery _)
    fun b _ ↦ ?_).mono (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := 1) (isQueryBoundP_liftComp_isEncQuery _)
    fun msgs _ ↦ ?_).mono (by omega)
  refine (isQueryBoundP_bind (n := 1) (m := 0) ?_ fun c _ ↦ ?_).mono (by omega)
  · simp [encQuery, IsEncQuery]
  · refine (isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_liftComp_isEncQuery _)
      fun _ _ ↦ ?_).mono (by omega)
    simp

/-- Against the real oracle, the reduction runs the one-time IND-CPA game. -/
lemma indDollarRealExperiment_oneTimeINDCPAReduction (scheme : DetSymmEncAlg M K C)
    (adv : scheme.toSymmEncAlg.IND_CPA_OneTime_Adversary) :
    scheme.indDollarRealExperiment (scheme.oneTimeINDCPAReduction adv) =
      SymmEncAlg.IND_CPA_OneTime_Game adv := by
  simp [indDollarRealExperiment, oneTimeINDCPAReduction, SymmEncAlg.IND_CPA_OneTime_Game]

/-- Against the ideal oracle, the challenge ciphertext is independent of the hidden bit, so the
reduction outputs `true` with probability exactly one half. -/
lemma evalDist_indDollarIdealExperiment_oneTimeINDCPAReduction_true [SampleableType C]
    (scheme : DetSymmEncAlg M K C) (adv : scheme.toSymmEncAlg.IND_CPA_OneTime_Adversary) :
    𝒟[indDollarIdealExperiment (scheme.oneTimeINDCPAReduction adv)] {true} = 1 / 2 := by
  let challenge : ProbComp Bool := do
    let msgs ← adv.chooseMessages
    let c ← $ᵗ C
    adv.distinguish msgs.2.2 c
  have hprogram : indDollarIdealExperiment (scheme.oneTimeINDCPAReduction adv) = (do
      let b ← ($ᵗ Bool)
      let z ← if b then challenge else challenge
      pure (b == z)) := by
    simp [challenge, indDollarIdealExperiment, oneTimeINDCPAReduction]
  have hbias := evalDist_boolBias_bind_uniformBool challenge challenge
  rw [← hprogram, Measure.boolDist_self,
    Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure] at hbias
  simpa using hbias

/-- One-time IND-CPA security of the induced scheme follows from IND$-CPA security against
one-query adversaries: the one-time IND-CPA advantage is exactly twice the IND$-CPA advantage of
`oneTimeINDCPAReduction`. The factor `2` comes from measuring one-time IND-CPA by the bias
`|Pr[b = b'] - Pr[b ≠ b']| = 2 * |Pr[b = b'] - 1/2|`, while the reduction's ideal world outputs
`true` with probability exactly `1/2`. -/
theorem IND_CPA_OneTime_Advantage_eq_two_mul_indDollarAdvantage [SampleableType C]
    (scheme : DetSymmEncAlg M K C) (adv : scheme.toSymmEncAlg.IND_CPA_OneTime_Adversary) :
    SymmEncAlg.IND_CPA_OneTime_Advantage adv =
      2 * scheme.indDollarAdvantage (scheme.oneTimeINDCPAReduction adv) := by
  rw [SymmEncAlg.IND_CPA_OneTime_Advantage, indDollarAdvantage,
    indDollarRealExperiment_oneTimeINDCPAReduction,
    Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure, Measure.boolDist,
    evalDist_indDollarIdealExperiment_oneTimeINDCPAReduction_true]

/-- If every IND$-CPA adversary making at most one encryption query has advantage at most `ε`,
then every one-time IND-CPA adversary against the induced scheme has advantage at most `2 * ε`. -/
theorem IND_CPA_OneTime_Advantage_le_of_indDollarAdvantage_le [SampleableType C]
    (scheme : DetSymmEncAlg M K C) {ε : ℝ≥0∞}
    (hsecure : ∀ adversary : INDDollarAdversary M C,
      IsQueryBoundP adversary IsEncQuery 1 → scheme.indDollarAdvantage adversary ≤ ε)
    (adv : scheme.toSymmEncAlg.IND_CPA_OneTime_Adversary) :
    SymmEncAlg.IND_CPA_OneTime_Advantage adv ≤ 2 * ε := by
  rw [IND_CPA_OneTime_Advantage_eq_two_mul_indDollarAdvantage]
  gcongr
  exact hsecure _ (scheme.isQueryBoundP_oneTimeINDCPAReduction adv)

end DetSymmEncAlg
