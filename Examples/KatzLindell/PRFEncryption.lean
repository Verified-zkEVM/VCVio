/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Examples.KatzLindell.Defs
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.Constructions.BitVec

/-!
# Katz–Lindell §3.5: Encryption from a Pseudorandom Function (Construction 3.30)

The randomized fixed-length private-key scheme `Enc_k(m) = (r, F_k(r) ⊕ m)` built from a
length-preserving pseudorandom function `F`, with a fresh uniform nonce `r ∈ {0,1}^n` per
encryption. This is the CPA-secure construction of §3.5.

- `prfEnc`: the construction over a PRF family `F`.
- `prfEnc_correct`: correctness — decryption recovers every message, since re-deriving `F_k(r)`
  from the transmitted nonce and XORing it off inverts the mask.

## Deferred scaffold

The security theorem `cpaSecure_prfEnc` (PRF-security plus a nonce-collision/birthday bound implies
IND-CPA) is **not** stated here because it needs the symmetric **IND-CPA left-right
encryption-oracle game former** — the §3.4 "multiple encryptions" definition — which is the largest
deferred definition of this pass and does not yet exist for `SymmEncAlg` (only the public-key
`AsymmEncAlg.IND_CPA` analogue does). The asymptotic **PRF distinguishing game** (a family/
`SecurityGame` wrapper over the single-scheme `prfRealExp`/`prfIdealExp` of
`VCVio.CryptoFoundations.PRF`, whose adversaries carry *oracle access* rather than a coin tape, so
they need a distinct polynomial-time notion) is likewise deferred. Both, together with the
spec-agnostic adjacent-game **hybrid builder** extracted from
`AsymmEncAlg/INDCPA/GenericLift.lean`, are the remaining §3.4/§3.5 scaffolding. The construction and
its correctness below are the concrete, discharged half.
-/

open ENNReal OracleComp OracleSpec SymmEncAlg PRFScheme

namespace KatzLindell

variable {K : ℕ → Type}

/-- **Katz–Lindell Construction 3.30**: the PRF-based randomized encryption scheme
`Enc_k(m) = (r, F_k(r) ⊕ m)` with a fresh uniform nonce `r ∈ {0,1}^n`. The ciphertext transmits
the nonce alongside the masked message; decryption re-derives `F_k(r)` and XORs it off. -/
noncomputable def prfEnc (F : (n : ℕ) → PRFScheme (K n) (BitVec n) (BitVec n)) :
    (n : ℕ) → SymmEncAlg ProbComp (BitVec n) (K n) (BitVec n × BitVec n) :=
  fun n =>
    { keygen := (F n).keygen
      encrypt := fun k m => do
        let r ← $ᵗ BitVec n
        pure (r, (F n).eval k r ^^^ m)
      decrypt := fun k c => pure (some ((F n).eval k c.1 ^^^ c.2)) }

/-- The PRF-based scheme is correct: decryption recovers every message, since the transmitted nonce
lets decryption reconstruct the exact keystream `F_k(r)` that masked the message, and `XOR` is
involutive. -/
theorem prfEnc_correct (F : (n : ℕ) → PRFScheme (K n) (BitVec n) (BitVec n)) :
    SchemeCorrect (prfEnc F) := by
  intro n msg
  have hsimp : (prfEnc F n).CompleteExp msg =
      (F n).keygen >>= fun _ => (do
        let _r ← $ᵗ BitVec n
        pure (some msg) : ProbComp (Option (BitVec n))) := by
    simp only [SymmEncAlg.CompleteExp, prfEnc, bind_assoc, pure_bind]
    refine bind_congr fun k => bind_congr fun r => ?_
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  rw [hsimp, probOutput_bind_const, probOutput_bind_const, probFailure_of_liftM_PMF,
    probFailure_of_liftM_PMF, probOutput_pure_self]
  simp

end KatzLindell
