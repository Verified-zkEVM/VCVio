/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.AsymmEncAlg.Defs
public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.Coercions.SubSpec.Basic
public import VCVio.OracleComp.Coercions.SubSpec.Measure
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics

/-!
# Fujisaki-Okamoto Shared Definitions

This file defines the shared objects used by the Fujisaki-Okamoto transform:

- explicit-coins PKEs as a specialization of `AsymmEncAlg`
- the induced randomized `AsymmEncAlg`
- spread notions and OW-CPA experiments for the `ProbComp` specialization: `OW_CPA_Experiment`,
  won when the guess is the challenge message, and `OW_CPA_PcoExperiment`, won when the challenge
  ciphertext decrypts to the guess
- OW-PCVA experiments for the general monadic interface, whose oracles `OW_PCVA_queryImpl` are a
  plaintext-checking oracle and a ciphertext-validity oracle that refuses the challenge:
  `OW_PCVA_Experiment` and `OW_PCVA_PcoExperiment` with the two win conditions,
  `OW_PCVA_DecryptionErrorExperiment` for the event that the challenge ciphertext does not decrypt
  to the challenge message, and `OW_PCVA_JointExperiment`, which observes all three in one run

The plaintext-checking win condition and the restricted validity oracle are those of
Hofheinz, Hövelmanns and Kiltz [HHK17], Definition 2.1 and Figure 3. Their remark on p. 8, that
the two win conditions differ by at most the correctness error, is `absDiff_OW_CPA_Advantage_le`
for OW-CPA; `OW_PCVA_Advantage_le_PcoAdvantage_add` and `OW_PCVA_PcoAdvantage_le_Advantage_add`
for OW-PCVA, with `OW_PCVA_DecryptionError` as the gap; and
`absDiff_OW_PCVA_Advantage_toAsymmEncAlg_le` for the randomized scheme induced by a `δ`-correct
explicit-coins scheme.

A `ProbCompRuntime` observes maps but need not respect binds, so the general OW-PCVA bounds assume
that the runtime does not observe the decryption of the challenge appended after the adversary.
That holds under every runtime when decryption makes no oracle query, and for every decryption
under a state-oracle runtime such as the random oracle model
(`OW_PCVA_Advantage_withStateOracle_eq`).

## References

* [HHK17] D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki-Okamoto
  Transformation*, TCC 2017, [ePrint 2017/604](https://eprint.iacr.org/2017/604), November 2, 2021
  revision: Definition 2.1 and Figure 3 (p. 8).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

universe u v

/-- On outcomes `(guess, msg, dec)`, a correct guess is either confirmed by the decryption or the
decryption is not `some msg`. -/
private lemma measure_guess_eq_le_add {M : Type} [MeasurableSpace (M × M × Option M)]
    (μ : Measure (M × M × Option M)) :
    μ {x | x.1 = x.2.1} ≤ μ {x | x.2.2 = some x.1} + μ {x | x.2.2 ≠ some x.2.1} := by
  refine (measure_mono fun (x : M × M × Option M) (hx : x.1 = x.2.1) => ?_).trans
    (measure_union_le _ _)
  by_cases hd : x.2.2 = some x.2.1
  · exact Or.inl (show x.2.2 = some x.1 by rw [hd, hx])
  · exact Or.inr hd

/-- On outcomes `(guess, msg, dec)`, a decryption to the guess either makes the guess correct or
is not `some msg`. -/
private lemma measure_dec_eq_le_add {M : Type} [MeasurableSpace (M × M × Option M)]
    (μ : Measure (M × M × Option M)) :
    μ {x | x.2.2 = some x.1} ≤ μ {x | x.1 = x.2.1} + μ {x | x.2.2 ≠ some x.2.1} := by
  refine (measure_mono fun (x : M × M × Option M) (hx : x.2.2 = some x.1) => ?_).trans
    (measure_union_le _ _)
  by_cases hd : x.2.2 = some x.2.1
  · exact Or.inl (show x.1 = x.2.1 from Option.some_injective _ (hx.symm.trans hd))
  · exact Or.inr hd

namespace AsymmEncAlg.ExplicitCoins

variable {M PK SK R C : Type}
  (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)

section Correct

variable [DecidableEq M] [SampleableType R]

/-- `delta`-correctness: failure in the canonical `AsymmEncAlg.correctnessExperiment` occurs with
probability at most `delta`. -/
def deltaCorrect (delta : ℝ≥0∞) : Prop :=
  ∀ msg : M, 𝒟[do
    let (pk, sk) ← pke.keygen
    let r ← ($ᵗ R)
    let c := pke.encrypt pk msg r
    let msg' := pke.decrypt sk c
    pure (decide (msg' = some msg))] {false} ≤ delta

end Correct

/-- `gamma`-spread: no ciphertext occurs with probability more than `gamma` for any fixed public
key and plaintext. -/
def gammaSpread [SampleableType R] (gamma : ℝ≥0∞) : Prop :=
  ∀ pk msg c, Pr{let r ← $ᵗ R}[pke.encrypt pk msg r = c] ≤ gamma

section OW_CPA

variable [SampleableType M] [SampleableType R] [DecidableEq M]

/-- Oracle interface for the one-way under chosen-plaintext attack (OW-CPA) experiment.

The sum `unifSpec + (M →ₒ C)` gives the adversary two capabilities:
- unrestricted uniform sampling from any sampleable type
- an encryption oracle on chosen plaintexts `M → C`
-/
def OW_CPA_oracleSpec (_pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C) :=
  unifSpec + (M →ₒ C)

/-- An OW-CPA adversary gets `pk`, a challenge ciphertext, and oracle access to chosen-plaintext
encryptions. -/
abbrev OW_CPA_Adversary := PK → C → OracleComp pke.OW_CPA_oracleSpec M

/-- Implementation of the OW-CPA encryption oracle. -/
def OW_CPA_queryImpl (pk : PK) : QueryImpl pke.OW_CPA_oracleSpec ProbComp :=
  QueryImpl.add unifSpec.passthrough
    (fun msg => do
      let r ← ($ᵗ R)
      pure (pke.encrypt pk msg r))

/-- Main one-way under chosen-plaintext attack (OW-CPA) experiment.

The experiment samples a fresh keypair and a uniform challenge message, forms the honest challenge
ciphertext via the induced randomized `AsymmEncAlg`, runs the adversary with oracle access
described by `OW_CPA_oracleSpec`, and returns `true` exactly when the adversary recovers the
challenge message. `OW_CPA_PcoExperiment` is the variant of HHK17, Figure 3, which checks the
guess by decrypting the challenge instead. -/
def OW_CPA_Experiment (adversary : pke.OW_CPA_Adversary) : ProbComp Bool := do
  let (pk, _sk) ← pke.keygen
  let msg ← $ᵗ M
  let r ← ($ᵗ R)
  let c := pke.encrypt pk msg r
  let msg' ← simulateQ (pke.OW_CPA_queryImpl pk) (adversary pk c)
  return decide (msg' = msg)

/-- OW-CPA advantage is the probability of recovering the sampled challenge plaintext. -/
noncomputable def OW_CPA_Advantage (adversary : pke.OW_CPA_Adversary) : ℝ≥0∞ :=
  𝒟[pke.OW_CPA_Experiment adversary] {true}

/-- The OW-CPA experiment of Hofheinz, Hövelmanns and Kiltz (HHK17, TCC 2017), Definition 2.1
and Figure 3, whose final step is the plaintext check `Pco(m', c*)`.

It runs as `OW_CPA_Experiment` and returns `true` exactly when the challenge ciphertext decrypts
to the adversary's guess. HHK17 (p. 8) remarks that this differs from the usual win condition,
`m' = m*`, by at most `δ` for a `δ`-correct scheme; see `absDiff_OW_CPA_Advantage_le`. -/
def OW_CPA_PcoExperiment (adversary : pke.OW_CPA_Adversary) : ProbComp Bool := do
  let (pk, sk) ← pke.keygen
  let msg ← $ᵗ M
  let r ← ($ᵗ R)
  let c := pke.encrypt pk msg r
  let msg' ← simulateQ (pke.OW_CPA_queryImpl pk) (adversary pk c)
  return decide (pke.decrypt sk c = some msg')

/-- The OW-CPA advantage of HHK17, Definition 2.1: the probability that the challenge ciphertext
decrypts to the adversary's guess in `OW_CPA_PcoExperiment`. -/
noncomputable def OW_CPA_PcoAdvantage (adversary : pke.OW_CPA_Adversary) : ℝ≥0∞ :=
  𝒟[pke.OW_CPA_PcoExperiment adversary] {true}

/-- Under `deltaCorrect δ`, after key generation, a uniform message, uniform coins and any further
computation whose result is discarded, the honest ciphertext fails to decrypt to the message with
probability at most `δ`. -/
private lemma prEvent_decrypt_ne_le {δ : ℝ≥0∞} (hδ : pke.deltaCorrect δ) {β : Type}
    (k : PK × SK → M → R → ProbComp β) :
    prEvent (pke.keygen >>= fun ks => ($ᵗ M) >>= fun msg => ($ᵗ R) >>= fun r =>
      (fun _ => pke.decrypt ks.2 (pke.encrypt ks.1 msg r) ≠ some msg) <$> k ks msg r) ≤ δ := by
  let : MeasurableSpace M := ⊤
  rw [OracleComp.prEvent_bind_bind_swap_of_uniform, prEvent_bind_of_discrete]
  refine (lintegral_mono fun msg => ?_).trans ((lintegral_const δ).trans_le
    (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)))
  have h := hδ msg
  rw [← prEvent_eq_evalDist_singleton] at h
  simp only [prEvent_norm, decide_eq_false_iff_not] at h
  refine le_of_eq_of_le ?_ h
  rw [prEvent_def, prEvent_def]
  congr 1
  refine evalDist_bind_congr _ _ _ fun ks => ?_
  rw [map_eq_bind_pure_comp]
  refine evalDist_bind_congr _ _ _ fun r => ?_
  rw [OracleComp.evalDist_map_const, Function.comp_apply, evalDist_pure]

/-- Both directions of the HHK17 (p. 8) remark for OW-CPA, on the joint execution returning the
guess, the challenge message and the decryption of the challenge. -/
private lemma OW_CPA_le_add_and_le_add {δ : ℝ≥0∞} (hδ : pke.deltaCorrect δ)
    (adversary : pke.OW_CPA_Adversary) :
    pke.OW_CPA_Advantage adversary ≤ pke.OW_CPA_PcoAdvantage adversary + δ ∧
      pke.OW_CPA_PcoAdvantage adversary ≤ pke.OW_CPA_Advantage adversary + δ := by
  let : MeasurableSpace (M × M × Option M) := ⊤
  let joint : ProbComp (M × M × Option M) := do
    let (pk, sk) ← pke.keygen
    let msg ← $ᵗ M
    let r ← ($ᵗ R)
    let c := pke.encrypt pk msg r
    let msg' ← simulateQ (pke.OW_CPA_queryImpl pk) (adversary pk c)
    return (msg', msg, pke.decrypt sk c)
  have hAdv : pke.OW_CPA_Advantage adversary = 𝒟[joint] {x | x.1 = x.2.1} := by
    rw [← prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_decide, OW_CPA_Advantage]
    simp only [OW_CPA_Experiment, joint, monad_norm]
  have hPco : pke.OW_CPA_PcoAdvantage adversary = 𝒟[joint] {x | x.2.2 = some x.1} := by
    rw [← prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_decide, OW_CPA_PcoAdvantage]
    simp only [OW_CPA_PcoExperiment, joint, monad_norm]
  have hErr : 𝒟[joint] {x | x.2.2 ≠ some x.2.1} ≤ δ := by
    rw [← prEvent_eq_evalDist_of_discrete]
    refine le_of_eq_of_le ?_ (pke.prEvent_decrypt_ne_le hδ fun ks msg r =>
      simulateQ (pke.OW_CPA_queryImpl ks.1) (adversary ks.1 (pke.encrypt ks.1 msg r)))
    simp only [joint, prEvent_norm]
  rw [hAdv, hPco]
  exact ⟨(measure_guess_eq_le_add _).trans (add_le_add le_rfl hErr),
    (measure_dec_eq_le_add _).trans (add_le_add le_rfl hErr)⟩

/-- **HHK17, p. 8 (OW-CPA).** For a `δ`-correct scheme, the usual OW-CPA advantage is at most the
OW-CPA advantage of HHK17, Definition 2.1, plus `δ`. -/
theorem OW_CPA_Advantage_le_PcoAdvantage_add {δ : ℝ≥0∞} (hδ : pke.deltaCorrect δ)
    (adversary : pke.OW_CPA_Adversary) :
    pke.OW_CPA_Advantage adversary ≤ pke.OW_CPA_PcoAdvantage adversary + δ :=
  (pke.OW_CPA_le_add_and_le_add hδ adversary).1

/-- **HHK17, p. 8 (OW-CPA).** For a `δ`-correct scheme, the OW-CPA advantage of HHK17,
Definition 2.1, is at most the usual OW-CPA advantage plus `δ`. -/
theorem OW_CPA_PcoAdvantage_le_Advantage_add {δ : ℝ≥0∞} (hδ : pke.deltaCorrect δ)
    (adversary : pke.OW_CPA_Adversary) :
    pke.OW_CPA_PcoAdvantage adversary ≤ pke.OW_CPA_Advantage adversary + δ :=
  (pke.OW_CPA_le_add_and_le_add hδ adversary).2

/-- **HHK17, p. 8 (OW-CPA).** For a `δ`-correct scheme, the usual OW-CPA advantage and the OW-CPA
advantage of HHK17, Definition 2.1, differ by at most `δ`. -/
theorem absDiff_OW_CPA_Advantage_le {δ : ℝ≥0∞} (hδ : pke.deltaCorrect δ)
    (adversary : pke.OW_CPA_Adversary) :
    ENNReal.absDiff (pke.OW_CPA_Advantage adversary) (pke.OW_CPA_PcoAdvantage adversary) ≤ δ :=
  ENNReal.absDiff_le_iff.2 (pke.OW_CPA_le_add_and_le_add hδ adversary)

end OW_CPA

end AsymmEncAlg.ExplicitCoins

section OW_PCVA

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK C : Type}

/-- Oracle interface for the one-way under plaintext-checking and validity attacks
(OW-PCVA) experiment.

The sum `spec + (((C × M) →ₒ Bool) + (C →ₒ Bool))` has three components:
- the ambient oracle interface `spec`
- the plaintext-checking oracle `Pco`, sending `(c, msg)` to whether `c` decrypts to `msg`
- the ciphertext-validity oracle `Cvo`, sending `c` to whether `c` decrypts to some plaintext

It is reducible, so the answer type of each checking query unfolds to `Bool`.
-/
abbrev OW_PCVA_oracleSpec (_encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) :=
  spec + (((C × M) →ₒ Bool) + (C →ₒ Bool))

/-- An OW-PCVA adversary gets the public key and challenge ciphertext, and outputs a plaintext
guess after querying the plaintext-checking and validity oracles. -/
abbrev OW_PCVA_Adversary (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) :=
  PK → C → OracleComp (OW_PCVA_oracleSpec encAlg) M

/-- Oracle implementation for OW-PCVA under the secret key `sk` and the challenge ciphertext
`cStar`, following Hofheinz, Hövelmanns and Kiltz (HHK17, TCC 2017), Definition 2.1 and Figure 3.

The plaintext-checking oracle `Pco(m, c)` decrypts `c` and answers whether the result is `m`, on
every ciphertext including the challenge. The ciphertext-validity oracle `Cvo(c)` answers whether
`c` decrypts to some plaintext. HHK17 (p. 8) restricts it to `c ≠ c*`; here a query on the
challenge is answered `false` without decrypting. -/
def OW_PCVA_queryImpl (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    [DecidableEq M] [DecidableEq C] (sk : SK) (cStar : C) :
    QueryImpl (OW_PCVA_oracleSpec encAlg) (OracleComp spec) :=
  let checkImpl : QueryImpl ((C × M) →ₒ Bool) (OracleComp spec) := fun (c, msg) => do
    let msg' ← encAlg.decrypt sk c
    return decide (msg' = some msg)
  let validImpl : QueryImpl (C →ₒ Bool) (OracleComp spec) := fun c =>
    if c = cStar then return false else do
      let msg' ← encAlg.decrypt sk c
      return msg'.isSome
  spec.passthrough + (checkImpl + validImpl)

/-- The validity oracle refuses the challenge ciphertext. -/
@[simp]
lemma OW_PCVA_queryImpl_valid_self (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    [DecidableEq M] [DecidableEq C] (sk : SK) (cStar : C) :
    OW_PCVA_queryImpl encAlg sk cStar (.inr (.inr cStar)) = return false := by
  simp only [OW_PCVA_queryImpl, QueryImpl.passthrough_add, QueryImpl.add_apply_inr, ↓reduceIte]

variable {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
  [SampleableType M] [DecidableEq M] [DecidableEq C]

/-- Main one-way under plaintext-checking and validity attacks (OW-PCVA) experiment, with the
usual win condition.

The experiment generates a keypair, samples a uniform challenge message, encrypts it honestly, and
then runs the adversary on the public key and challenge ciphertext with the oracles of
`OW_PCVA_queryImpl`. It returns `true` exactly when the final guess equals the challenge message.
`OW_PCVA_PcoExperiment` is the variant of HHK17, Figure 3, which checks the guess by decrypting the
challenge instead. -/
noncomputable def OW_PCVA_Experiment
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : OW_PCVA_Adversary encAlg) : OracleComp spec Bool := do
  let (pk, sk) ← encAlg.keygen
  let msg ← runtime.liftProbComp ($ᵗ M)
  let cStar ← encAlg.encrypt pk msg
  let msg' ← simulateQ (OW_PCVA_queryImpl encAlg sk cStar) (adversary pk cStar)
  return decide (msg' = msg)

/-- OW-PCVA advantage is the message-recovery probability in `OW_PCVA_Experiment`. -/
noncomputable def OW_PCVA_Advantage
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : OW_PCVA_Adversary encAlg) : ℝ≥0∞ :=
  runtime.evalDist (OW_PCVA_Experiment runtime adversary) {true}

/-- The OW-PCVA experiment of Hofheinz, Hövelmanns and Kiltz (HHK17, TCC 2017), Definition 2.1
and Figure 3, whose final step is the plaintext check `Pco(m', c*)`.

It runs as `OW_PCVA_Experiment`, with the same oracles, and then decrypts the challenge ciphertext
`cStar`. It returns `true` exactly when `cStar` decrypts to the adversary's guess. HHK17 (p. 8)
remarks that this differs from the usual win condition, `m' = m*`, by at most the correctness
error of the scheme; `OW_PCVA_Advantage_le_PcoAdvantage_add` and
`OW_PCVA_PcoAdvantage_le_Advantage_add` bound the difference by `OW_PCVA_DecryptionError`. -/
noncomputable def OW_PCVA_PcoExperiment
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : OW_PCVA_Adversary encAlg) : OracleComp spec Bool := do
  let (pk, sk) ← encAlg.keygen
  let msg ← runtime.liftProbComp ($ᵗ M)
  let cStar ← encAlg.encrypt pk msg
  let msg' ← simulateQ (OW_PCVA_queryImpl encAlg sk cStar) (adversary pk cStar)
  let dec ← encAlg.decrypt sk cStar
  return decide (dec = some msg')

/-- The OW-PCVA advantage of HHK17, Definition 2.1: the probability that the challenge ciphertext
decrypts to the adversary's guess in `OW_PCVA_PcoExperiment`. -/
noncomputable def OW_PCVA_PcoAdvantage
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : OW_PCVA_Adversary encAlg) : ℝ≥0∞ :=
  runtime.evalDist (OW_PCVA_PcoExperiment runtime adversary) {true}

/-- Decryption-error experiment for OW-PCVA: it runs as `OW_PCVA_PcoExperiment` and returns `true`
exactly when the challenge ciphertext does not decrypt to the challenge message. -/
noncomputable def OW_PCVA_DecryptionErrorExperiment
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : OW_PCVA_Adversary encAlg) : OracleComp spec Bool := do
  let (pk, sk) ← encAlg.keygen
  let msg ← runtime.liftProbComp ($ᵗ M)
  let cStar ← encAlg.encrypt pk msg
  let _ ← simulateQ (OW_PCVA_queryImpl encAlg sk cStar) (adversary pk cStar)
  let dec ← encAlg.decrypt sk cStar
  return decide (dec ≠ some msg)

/-- The probability that the challenge ciphertext does not decrypt to the challenge message after
the adversary has run, in `OW_PCVA_DecryptionErrorExperiment`. It is the gap between
`OW_PCVA_Advantage` and `OW_PCVA_PcoAdvantage`. -/
noncomputable def OW_PCVA_DecryptionError
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : OW_PCVA_Adversary encAlg) : ℝ≥0∞ :=
  runtime.evalDist (OW_PCVA_DecryptionErrorExperiment runtime adversary) {true}

/-- Joint OW-PCVA experiment: it runs as `OW_PCVA_PcoExperiment` and returns the adversary's guess,
the challenge message and the decryption of the challenge ciphertext.

`OW_PCVA_PcoExperiment` and `OW_PCVA_DecryptionErrorExperiment` are maps of it. The usual win event
`guess = msg` of `OW_PCVA_Experiment`, which does not decrypt the challenge, is an event of it
whenever the runtime does not observe the trailing decryption. -/
noncomputable def OW_PCVA_JointExperiment
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : OW_PCVA_Adversary encAlg) : OracleComp spec (M × M × Option M) := do
  let (pk, sk) ← encAlg.keygen
  let msg ← runtime.liftProbComp ($ᵗ M)
  let cStar ← encAlg.encrypt pk msg
  let msg' ← simulateQ (OW_PCVA_queryImpl encAlg sk cStar) (adversary pk cStar)
  let dec ← encAlg.decrypt sk cStar
  return (msg', msg, dec)

section relation

variable (runtime : ProbCompRuntime (OracleComp spec)) (adversary : OW_PCVA_Adversary encAlg)

/-- `OW_PCVA_PcoExperiment` observes whether the joint decryption of the challenge is the
guess. -/
lemma OW_PCVA_PcoExperiment_eq_map :
    OW_PCVA_PcoExperiment runtime adversary =
      (fun x => decide (x.2.2 = some x.1)) <$> OW_PCVA_JointExperiment runtime adversary := by
  simp only [OW_PCVA_PcoExperiment, OW_PCVA_JointExperiment, monad_norm, Function.comp_apply]

/-- `OW_PCVA_DecryptionErrorExperiment` observes whether the joint decryption of the challenge
differs from the challenge message. -/
lemma OW_PCVA_DecryptionErrorExperiment_eq_map :
    OW_PCVA_DecryptionErrorExperiment runtime adversary =
      (fun x => decide (x.2.2 ≠ some x.2.1)) <$> OW_PCVA_JointExperiment runtime adversary := by
  simp only [OW_PCVA_DecryptionErrorExperiment, OW_PCVA_JointExperiment, monad_norm,
    Function.comp_apply]

/-- The mass a runtime puts on a decided predicate being `true` is the mass of its event. -/
private lemma evalDist_map_decide_true {m : Type → Type v} [Monad m] (runtime : ProbCompRuntime m)
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx : m α) (p : α → Prop)
    [DecidablePred p] :
    runtime.evalDist ((fun x => decide (p x)) <$> mx) {true} = runtime.evalDist mx {x | p x} := by
  rw [runtime.evalDist_map _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
  congr 1
  ext x
  simp

/-- **HHK17, p. 8 (usual game against Pco game).** The usual OW-PCVA advantage is at most the
OW-PCVA advantage of HHK17, Definition 2.1, plus the decryption error of the challenge.

The hypothesis `h` says that the usual win event is no likelier in `OW_PCVA_Experiment` than in
`OW_PCVA_JointExperiment`, which also decrypts the challenge after the adversary. A general
runtime need not satisfy it, since it may lose mass on that trailing decryption.
`OW_PCVA_Experiment_eq_map_of_decrypt_eq_pure` gives it with equality for every runtime when
decryption is query-free, and `OW_PCVA_Advantage_withStateOracle_eq` for every state-oracle
runtime, the random oracle model included. -/
theorem OW_PCVA_Advantage_le_PcoAdvantage_add
    (h : OW_PCVA_Advantage runtime adversary ≤ runtime.evalDist
      ((fun x => decide (x.1 = x.2.1)) <$> OW_PCVA_JointExperiment runtime adversary) {true}) :
    OW_PCVA_Advantage runtime adversary ≤
      OW_PCVA_PcoAdvantage runtime adversary + OW_PCVA_DecryptionError runtime adversary := by
  let : MeasurableSpace (M × M × Option M) := ⊤
  refine h.trans ?_
  rw [OW_PCVA_PcoAdvantage, OW_PCVA_DecryptionError, OW_PCVA_PcoExperiment_eq_map,
    OW_PCVA_DecryptionErrorExperiment_eq_map, evalDist_map_decide_true, evalDist_map_decide_true,
    evalDist_map_decide_true]
  exact measure_guess_eq_le_add _

/-- **HHK17, p. 8 (Pco game against usual game).** The OW-PCVA advantage of HHK17,
Definition 2.1, is at most the usual OW-PCVA advantage plus the decryption error of the
challenge.

The hypothesis `h` says that the usual win event is no likelier in `OW_PCVA_JointExperiment`,
which decrypts the challenge after the adversary, than in `OW_PCVA_Experiment`; see
`OW_PCVA_Advantage_le_PcoAdvantage_add` for when it holds. -/
theorem OW_PCVA_PcoAdvantage_le_Advantage_add
    (h : runtime.evalDist ((fun x => decide (x.1 = x.2.1)) <$>
      OW_PCVA_JointExperiment runtime adversary) {true} ≤ OW_PCVA_Advantage runtime adversary) :
    OW_PCVA_PcoAdvantage runtime adversary ≤
      OW_PCVA_Advantage runtime adversary + OW_PCVA_DecryptionError runtime adversary := by
  let : MeasurableSpace (M × M × Option M) := ⊤
  refine le_trans ?_ (add_le_add h le_rfl)
  rw [OW_PCVA_PcoAdvantage, OW_PCVA_DecryptionError, OW_PCVA_PcoExperiment_eq_map,
    OW_PCVA_DecryptionErrorExperiment_eq_map, evalDist_map_decide_true, evalDist_map_decide_true,
    evalDist_map_decide_true]
  exact measure_dec_eq_le_add _

/-- When decryption makes no oracle query, the usual OW-PCVA experiment is the usual win event of
`OW_PCVA_JointExperiment`, under every runtime. -/
lemma OW_PCVA_Experiment_eq_map_of_decrypt_eq_pure (dec : SK → C → Option M)
    (hdec : ∀ sk c, encAlg.decrypt sk c = pure (dec sk c)) :
    OW_PCVA_Experiment runtime adversary =
      (fun x => decide (x.1 = x.2.1)) <$> OW_PCVA_JointExperiment runtime adversary := by
  simp only [OW_PCVA_Experiment, OW_PCVA_JointExperiment, hdec, monad_norm, Function.comp_apply]

/-- **HHK17, p. 8, query-free decryption.** When decryption makes no oracle query, the usual
OW-PCVA advantage is at most the HHK17 advantage plus the decryption error, under every
runtime. -/
theorem OW_PCVA_Advantage_le_PcoAdvantage_add_of_decrypt_eq_pure (dec : SK → C → Option M)
    (hdec : ∀ sk c, encAlg.decrypt sk c = pure (dec sk c)) :
    OW_PCVA_Advantage runtime adversary ≤
      OW_PCVA_PcoAdvantage runtime adversary + OW_PCVA_DecryptionError runtime adversary :=
  OW_PCVA_Advantage_le_PcoAdvantage_add runtime adversary <| by
    rw [OW_PCVA_Advantage, OW_PCVA_Experiment_eq_map_of_decrypt_eq_pure runtime adversary dec hdec]

/-- **HHK17, p. 8, query-free decryption.** When decryption makes no oracle query, the HHK17
OW-PCVA advantage is at most the usual advantage plus the decryption error, under every
runtime. -/
theorem OW_PCVA_PcoAdvantage_le_Advantage_add_of_decrypt_eq_pure (dec : SK → C → Option M)
    (hdec : ∀ sk c, encAlg.decrypt sk c = pure (dec sk c)) :
    OW_PCVA_PcoAdvantage runtime adversary ≤
      OW_PCVA_Advantage runtime adversary + OW_PCVA_DecryptionError runtime adversary :=
  OW_PCVA_PcoAdvantage_le_Advantage_add runtime adversary <| by
    rw [OW_PCVA_Advantage, OW_PCVA_Experiment_eq_map_of_decrypt_eq_pure runtime adversary dec hdec]

end relation

section withStateOracle

variable {κ : Type} {hashSpec : OracleSpec κ} {σ : Type}
  (hashImpl : QueryImpl hashSpec (StateT σ ProbComp)) (s : σ)

/-- A state-oracle runtime does not observe a computation whose result is discarded: its
simulation runs in `ProbComp`, which never fails. -/
private lemma withStateOracle_evalDist_bind_discard {α β γ : Type} [MeasurableSpace γ]
    (mx : OracleComp (unifSpec + hashSpec) α) (k : α → OracleComp (unifSpec + hashSpec) β)
    (f : α → γ) :
    (ProbCompRuntime.withStateOracle hashImpl s).evalDist
        (mx >>= fun a => k a >>= fun _ => pure (f a)) =
      (ProbCompRuntime.withStateOracle hashImpl s).evalDist (mx >>= fun a => pure (f a)) := by
  rw [ProbCompRuntime.withStateOracle_evalDist, ProbCompRuntime.withStateOracle_evalDist]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure,
    map_bind, map_pure]
  exact evalDist_bind_congr _ _ _ fun _ => OracleComp.evalDist_bind_const _ _

/-- Under a state-oracle runtime, in particular the random oracle model
`ProbCompRuntime.rom`, the usual OW-PCVA advantage is the probability of the usual win event of
`OW_PCVA_JointExperiment`, whatever oracles decryption queries. This discharges the hypotheses of
`OW_PCVA_Advantage_le_PcoAdvantage_add` and `OW_PCVA_PcoAdvantage_le_Advantage_add`. -/
theorem OW_PCVA_Advantage_withStateOracle_eq
    {encAlg : AsymmEncAlg (OracleComp (unifSpec + hashSpec)) M PK SK C}
    (adversary : OW_PCVA_Adversary encAlg) :
    OW_PCVA_Advantage (ProbCompRuntime.withStateOracle hashImpl s) adversary =
      (ProbCompRuntime.withStateOracle hashImpl s).evalDist
        ((fun x => decide (x.1 = x.2.1)) <$>
          OW_PCVA_JointExperiment (ProbCompRuntime.withStateOracle hashImpl s) adversary)
        {true} := by
  set runtime := ProbCompRuntime.withStateOracle hashImpl s
  let prefixExp : OracleComp (unifSpec + hashSpec) (M × M × SK × C) := do
    let (pk, sk) ← encAlg.keygen
    let msg ← runtime.liftProbComp ($ᵗ M)
    let cStar ← encAlg.encrypt pk msg
    let msg' ← simulateQ (OW_PCVA_queryImpl encAlg sk cStar) (adversary pk cStar)
    return (msg', msg, sk, cStar)
  have hExp : OW_PCVA_Experiment runtime adversary =
      prefixExp >>= fun t => pure (decide (t.1 = t.2.1)) := by
    simp only [OW_PCVA_Experiment, prefixExp, monad_norm]
  have hJoint : (fun x => decide (x.1 = x.2.1)) <$> OW_PCVA_JointExperiment runtime adversary =
      prefixExp >>= fun t => encAlg.decrypt t.2.2.1 t.2.2.2 >>= fun _ =>
        pure (decide (t.1 = t.2.1)) := by
    simp only [OW_PCVA_JointExperiment, prefixExp, monad_norm, Function.comp_apply]
  rw [OW_PCVA_Advantage, hExp, hJoint, withStateOracle_evalDist_bind_discard]

end withStateOracle

end OW_PCVA

namespace AsymmEncAlg.ExplicitCoins

variable {M PK SK R C : Type} (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
  [SampleableType M] [SampleableType R] [DecidableEq M] [DecidableEq C]

/-! ## OW-PCVA for the induced randomized scheme

The induced randomized scheme `pke.toAsymmEncAlg ProbCompRuntime.probComp` decrypts without
oracle queries, so the two OW-PCVA win conditions differ by its decryption error, which
`δ`-correctness bounds. -/

/-- For a `δ`-correct scheme, the OW-PCVA decryption error of the induced randomized scheme is at
most `δ`. -/
theorem OW_PCVA_DecryptionError_toAsymmEncAlg_le {δ : ℝ≥0∞} (hδ : pke.deltaCorrect δ)
    (adversary : OW_PCVA_Adversary (pke.toAsymmEncAlg ProbCompRuntime.probComp)) :
    OW_PCVA_DecryptionError ProbCompRuntime.probComp adversary ≤ δ := by
  have hlift : ∀ {α : Type} (x : ProbComp α),
      ProbCompRuntime.probComp.liftProbComp.toFun α x = x := fun _ => rfl
  rw [OW_PCVA_DecryptionError, ProbCompRuntime.probComp_evalDist,
    ← prEvent_eq_evalDist_singleton]
  refine le_of_eq_of_le ?_ (pke.prEvent_decrypt_ne_le hδ fun ks msg r =>
    simulateQ (OW_PCVA_queryImpl (pke.toAsymmEncAlg ProbCompRuntime.probComp) ks.2
      (pke.encrypt ks.1 msg r)) (adversary ks.1 (pke.encrypt ks.1 msg r)))
  simp only [OW_PCVA_DecryptionErrorExperiment, toAsymmEncAlg, hlift, prEvent_norm,
    decide_eq_true_eq]

/-- **HHK17, p. 8 (OW-PCVA).** For a `δ`-correct scheme, the usual OW-PCVA advantage against the
induced randomized scheme is at most its OW-PCVA advantage of HHK17, Definition 2.1, plus `δ`. -/
theorem OW_PCVA_Advantage_toAsymmEncAlg_le_PcoAdvantage_add {δ : ℝ≥0∞}
    (hδ : pke.deltaCorrect δ)
    (adversary : OW_PCVA_Adversary (pke.toAsymmEncAlg ProbCompRuntime.probComp)) :
    OW_PCVA_Advantage ProbCompRuntime.probComp adversary ≤
      OW_PCVA_PcoAdvantage ProbCompRuntime.probComp adversary + δ :=
  (OW_PCVA_Advantage_le_PcoAdvantage_add_of_decrypt_eq_pure _ adversary pke.decrypt
    fun _ _ => rfl).trans (add_le_add le_rfl (pke.OW_PCVA_DecryptionError_toAsymmEncAlg_le hδ _))

/-- **HHK17, p. 8 (OW-PCVA).** For a `δ`-correct scheme, the OW-PCVA advantage of HHK17,
Definition 2.1, against the induced randomized scheme is at most its usual OW-PCVA advantage plus
`δ`. -/
theorem OW_PCVA_PcoAdvantage_toAsymmEncAlg_le_Advantage_add {δ : ℝ≥0∞}
    (hδ : pke.deltaCorrect δ)
    (adversary : OW_PCVA_Adversary (pke.toAsymmEncAlg ProbCompRuntime.probComp)) :
    OW_PCVA_PcoAdvantage ProbCompRuntime.probComp adversary ≤
      OW_PCVA_Advantage ProbCompRuntime.probComp adversary + δ :=
  (OW_PCVA_PcoAdvantage_le_Advantage_add_of_decrypt_eq_pure _ adversary pke.decrypt
    fun _ _ => rfl).trans (add_le_add le_rfl (pke.OW_PCVA_DecryptionError_toAsymmEncAlg_le hδ _))

/-- **HHK17, p. 8 (OW-PCVA).** For a `δ`-correct scheme, the usual OW-PCVA advantage against the
induced randomized scheme and its OW-PCVA advantage of HHK17, Definition 2.1, differ by at most
`δ`. -/
theorem absDiff_OW_PCVA_Advantage_toAsymmEncAlg_le {δ : ℝ≥0∞} (hδ : pke.deltaCorrect δ)
    (adversary : OW_PCVA_Adversary (pke.toAsymmEncAlg ProbCompRuntime.probComp)) :
    ENNReal.absDiff (OW_PCVA_Advantage ProbCompRuntime.probComp adversary)
      (OW_PCVA_PcoAdvantage ProbCompRuntime.probComp adversary) ≤ δ :=
  ENNReal.absDiff_le_iff.2 ⟨pke.OW_PCVA_Advantage_toAsymmEncAlg_le_PcoAdvantage_add hδ adversary,
    pke.OW_PCVA_PcoAdvantage_toAsymmEncAlg_le_Advantage_add hδ adversary⟩

end AsymmEncAlg.ExplicitCoins
