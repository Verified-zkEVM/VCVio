/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Wots
import Mathlib.Data.List.GetD

/-!
# WOTS+ Message-Encoding Injectivity

The full-width WOTS+ message encoding of FIPS 205 Algorithms 7 and 8 (lines 1–7) determines the
node being signed, and any two distinct nodes have a chain on which the first node's step count
is strictly smaller than the second's.

Two facts combine here. `WotsEncoding.base2b_msg_injective` shows that under the alignment
obligation `lgw ∣ 8n` of `Params.Valid` the `len1` message digits lose no bit of the `n`-byte
message; `CorePrimitives.ByteLaws` transports that from the byte encoding to the abstract node
carrier `core.Y`. `WotsChecksum.wots_fullDigits_incomparable` is the purely combinatorial
statement that distinct message-digit vectors yield pointwise-incomparable full digit vectors.
Together they give `chainLengthsCore_incomparable` and its index-wise form
`chainStepsCore_two_encodings`: for `msg ≠ msg'` some chain index `i < len` has
`chainStepsCore core msg i < chainStepsCore core msg' i`. That statement is the Lean
counterpart of the `two_encodings` axiom of the EasyCrypt SPHINCS+ proof (`WOTS_TW_ES.ec`),
which is the only fact about the message encoding that proof assumes; here it is proved for the
concrete FIPS 205 encoding, under `p.Valid` and `core.ByteLaws`.

The same incomparability, applied against a second message-digit vector, shows that every node has
a chain whose step count is strictly below the top step `w - 1`
(`exists_chainStepsCore_lt_pred_w`).

## References

- NIST FIPS 205, §5.2–5.3 (Algorithms 7 and 8)
-/

public section

namespace SLHDSA

open WotsChecksum
open WotsEncoding

variable {p : Params} {core : CorePrimitives p}

/-- Full-width message-encoding injectivity: under the alignment obligation of `Params.Valid`
and byte coherence of the node carrier, the `len1` message digits determine the node. -/
theorem wotsMsgDigitsCore_injective (valid : p.Valid) (laws : core.ByteLaws) :
    Function.Injective (wotsMsgDigitsCore core) := by
  intro x y h
  have h' : base2b (core.yToBytes x).toList p.lgw p.len1 =
      base2b (core.yToBytes y).toList p.lgw p.len1 := h
  exact laws.yToBytes_injective (base2b_msg_injective valid h')

/-- The complete `len`-digit chain-length vector (message digits followed by the FIPS checksum
digits) determines the node. -/
theorem chainLengthsCore_injective (valid : p.Valid) (laws : core.ByteLaws) :
    Function.Injective (chainLengthsCore core) :=
  (fullDigits_injective p).comp (wotsMsgDigitsCore_injective valid laws)

/-- Distinct nodes have pointwise-incomparable chain-length vectors: neither is pointwise `≤`
the other. This combines `wotsMsgDigitsCore_injective` (distinct nodes have distinct message
digits) with `WotsChecksum.wots_fullDigits_incomparable`. -/
theorem chainLengthsCore_incomparable (valid : p.Valid) (laws : core.ByteLaws)
    {msg msg' : core.Y} (hne : msg ≠ msg') :
    ¬ List.Forall₂ (· ≤ ·) (chainLengthsCore core msg) (chainLengthsCore core msg') ∧
    ¬ List.Forall₂ (· ≤ ·) (chainLengthsCore core msg') (chainLengthsCore core msg) := by
  simp only [chainLengthsCore_eq_wotsFullDigits valid]
  exact wots_fullDigits_incomparable
    (wotsMsgDigitsCore_length core msg) (wotsMsgDigitsCore_length core msg')
    (wotsMsgDigitsCore_mem_lt core msg) (wotsMsgDigitsCore_mem_lt core msg')
    valid.len1_mul_pred_w_lt_pow_len2
    (fun h => hne ((wotsMsgDigitsCore_injective valid laws) h))

/-- Two distinct nodes have a chain index at which the first node's step count is strictly
smaller than the second's. This is the combinatorial ingredient a WOTS+ unforgeability
reduction consumes, instantiated with the forgery target as `msg` and the honestly signed
message as `msg'`: at the witnessing index the target's step count is strictly below the
signed one, so a forger who only advances the honest signer's chains cannot reach the target's
encoding. The EasyCrypt SPHINCS+ proof's forgery-side use of its axiom is exactly this swapped
form (`two_encodings m' m` in `nhchwcoll_hchwpre`, `WOTS_TW_ES.ec`). The statement is the
index-wise reading of the second conjunct of `chainLengthsCore_incomparable`, and the Lean
counterpart of the EasyCrypt `two_encodings` axiom. -/
theorem chainStepsCore_two_encodings (valid : p.Valid) (laws : core.ByteLaws)
    {msg msg' : core.Y} (hne : msg ≠ msg') :
    ∃ i, i < p.len ∧ chainStepsCore core msg i < chainStepsCore core msg' i := by
  by_contra hnot
  have hle : ∀ i, i < p.len → chainStepsCore core msg' i ≤ chainStepsCore core msg i :=
    fun i hi => Nat.le_of_not_lt fun hlt => hnot ⟨i, hi, hlt⟩
  exact (chainLengthsCore_incomparable valid laws hne).2
    (List.forall₂_of_length_eq_of_get (by simp) fun i hi hi' => by
      rw [← List.getD_eq_get (l := chainLengthsCore core msg') (d := 0) ⟨i, hi⟩,
        ← List.getD_eq_get (l := chainLengthsCore core msg) (d := 0) ⟨i, hi'⟩]
      exact hle i (by simpa using hi))

/-- Every node has a chain index `i < len` whose step count is strictly below the top step
`w - 1`, at every validated parameter set and with no hypothesis on the node type `core.Y`. -/
theorem exists_chainStepsCore_lt_pred_w (valid : p.Valid) (msg : core.Y) :
    ∃ i < p.len, chainStepsCore core msg i < p.w - 1 := by
  by_contra hnot
  have htop : ∀ i, i < p.len → p.w - 1 ≤ chainStepsCore core msg i :=
    fun i hi => Nat.le_of_not_lt fun hlt => hnot ⟨i, hi, hlt⟩
  have hw : 1 < p.w := Nat.one_lt_two_pow (Nat.ne_of_gt valid.lgw_pos)
  have hl1 : 0 < p.len1 := Nat.div_pos (by have := valid.n_pos; omega) valid.lgw_pos
  set dig := wotsMsgDigitsCore core msg
  obtain ⟨dig', hlen', hlt', hne⟩ : ∃ dig' : List ℕ,
      dig'.length = p.len1 ∧ (∀ d ∈ dig', d < p.w) ∧ dig' ≠ dig := by
    by_cases h0 : dig = List.replicate p.len1 0
    · refine ⟨List.replicate p.len1 1, List.length_replicate, fun d hd => ?_, fun h => ?_⟩
      · rw [List.eq_of_mem_replicate hd]
        exact hw
      · rw [h0] at h
        have := congrArg List.sum h
        simp only [List.sum_replicate, smul_eq_mul, mul_one, mul_zero] at this
        omega
    · exact ⟨List.replicate p.len1 0, List.length_replicate,
        fun d hd => (List.eq_of_mem_replicate hd).symm ▸ Params.w_pos p, Ne.symm h0⟩
  refine (wots_fullDigits_incomparable hlen' (wotsMsgDigitsCore_length core msg) hlt'
    (wotsMsgDigitsCore_mem_lt core msg) valid.len1_mul_pred_w_lt_pow_len2 hne).1 ?_
  rw [← chainLengthsCore_eq_wotsFullDigits valid, ← fullDigits_eq_wotsFullDigits valid _ hlen' hlt']
  refine List.forall₂_of_length_eq_of_get (by simp [hlen']) fun i hi hi' => ?_
  have hd := fullDigits_lt p dig' hlt' _ (List.getElem_mem hi)
  have hs := htop i (by simpa using hi')
  rw [chainStepsCore, List.getD_eq_getElem _ _ hi'] at hs
  simp only [List.get_eq_getElem]
  omega

end SLHDSA
