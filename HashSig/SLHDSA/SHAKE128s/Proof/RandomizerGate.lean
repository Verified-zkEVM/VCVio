/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.CacheAvailability
public import HashSig.SLHDSA.SHAKE128s.Proof.SecretGuessCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.HashSeparation
public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge

/-!
# The `PRF_msg` class

`CacheAvailability.signedAt` counts a digest as disclosing only when the cache also holds the
`PRF_msg` entry the signer would have made for that message. That closes the hole where an
adversary declares its own positions disclosed by querying a digest under a randomiser of its
own — but it opens a gate, because `Hashing.randomizerInput prf seed message` is
`prf ‖ seed ‖ message` and carries `SK.prf` in the clear. A run that queries there manufactures
the entry.

That query is a guess at `SK.prf` and is charged as one, at one unit of `2 ^ -128` per queried
input, against a secret drawn after the run. This file defines the class (`PrfClass`), the seed
a `PRF_msg` input carries (`prfGuess`, recovered from its first block, which the format
determines because `bytesBE n` is injective), and the facts about it that the charge uses.

**The class does not meet the canonical one.** A canonical input is `PK.seed ‖ address ‖
payload` and a `PRF_msg` input is `SK.prf ‖ PK.seed ‖ message`; their first blocks are the two
seeds, so unless the seeds coincide no input is both (`canonicalInput_ne_randomizerInput`). The
coincidence `SK.prf = PK.seed` is itself one unit of `2 ^ -128`.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RandomizerGate

open CanonicalGraph

/-! ## The seed a `PRF_msg` input carries -/

/-- **The first block of a `PRF_msg` input is its seed.** -/
theorem randomizerInput_prf_inj {prf prf' seed seed' : Digest} {message message' : Bytes}
    (hequal : Hashing.randomizerInput prf seed message =
      Hashing.randomizerInput prf' seed' message') : prf = prf' := by
  have hsplit : bytesBE n prf ++ (bytesBE n seed ++ message) =
      bytesBE n prf' ++ (bytesBE n seed' ++ message') := by
    simpa only [Hashing.randomizerInput, List.append_assoc] using hequal
  exact bytesBE_injective n (List.append_inj hsplit (by simp)).1

open scoped Classical in
/-- The seed a `PRF_msg` input carries in the clear, read off its first block. -/
@[expose] noncomputable def prfGuess (input : Bytes) : Digest :=
  if hformat : ∃ (prf seed : Digest) (message : Bytes),
    input = Hashing.randomizerInput prf seed message then hformat.choose else default

/-- The seed read off a `PRF_msg` input is the `SK.prf` it was formed with. -/
theorem prfGuess_randomizerInput (prf seed : Digest) (message : Bytes) :
    prfGuess (Hashing.randomizerInput prf seed message) = prf := by
  classical
  have hformat : ∃ (candidate other : Digest) (payload : Bytes),
      Hashing.randomizerInput prf seed message =
        Hashing.randomizerInput candidate other payload := ⟨prf, seed, message, rfl⟩
  rw [prfGuess, dite_eq_left hformat]
  obtain ⟨other, payload, hspec⟩ := hformat.choose_spec
  exact (randomizerInput_prf_inj hspec).symm

/-! ## The two classes do not meet -/

/-- **A canonical input is not a `PRF_msg` input**, the two seeds being distinct: their first
blocks are the seeds themselves. -/
theorem canonicalInput_ne_randomizerInput (publicSeed prfSeed seed : Digest) (cells : Cells)
    (parent : StructuralNode) (message : Bytes) (hne : prfSeed ≠ publicSeed) :
    canonicalInput publicSeed cells parent ≠ Hashing.randomizerInput prfSeed seed message :=
  fun hequal => HashSeparation.randomizer_tweakable_ne hne hequal.symm

/-! ## Where the separation stops

The gate's class is disjoint from the canonical one because the two formats open with different
seeds. It is **not** disjoint from the message class, and the reason is the shared oracle: a
message input *is* a `PRF_msg` input, at its own randomiser read as the seed and the public root
absorbed into the message. FIPS 205 separates `PRF_msg` from `H_msg` as functions; this model
idealises both as one oracle on byte strings, and only the first block distinguishes them.

So the signer's own digest query is a `PRF_msg` input at the real seed exactly when the
randomiser it derived for that message is the seed — an answer hitting a secret, which the
signer's queries can do once per request. -/

/-- **A message input is a `PRF_msg` input.** -/
theorem messageInput_eq_randomizerInput (randomizer : Digest) (pk : PublicKey)
    (message : Bytes) :
    Hashing.messageInput randomizer pk message =
      Hashing.randomizerInput randomizer pk.seed (bytesBE n pk.root ++ message) := by
  simp only [Hashing.messageInput, Hashing.randomizerInput, List.append_assoc]

/-- **And it is one at a given seed exactly when its randomiser is that seed.** -/
theorem messageInput_eq_randomizerInput_iff (randomizer prfSeed seed : Digest) (pk : PublicKey)
    (message payload : Bytes) :
    Hashing.messageInput randomizer pk message =
        Hashing.randomizerInput prfSeed seed payload →
      randomizer = prfSeed := by
  rw [messageInput_eq_randomizerInput]
  exact randomizerInput_prf_inj

/-! ## The answer side of the same class

The gate is about an input the adversary writes; its neighbour is about an answer the *signer*
receives. A served request's randomiser is the truncation of a fresh answer at a `PRF_msg`
input, and if that truncation is the seed itself then the signer's own digest query becomes a
`PRF_msg` input at the real seed — which is how a disclosure can be manufactured with no request
behind it. A fresh answer truncates to a fixed digest with probability `2 ^ -128`, and only
inputs of the class can fire the event. -/

/-- The inputs whose first block is a given seed. -/
@[expose] def PrfClass (prfSeed : Digest) (input : Bytes) : Prop :=
  ∃ (seed : Digest) (message : Bytes), input = Hashing.randomizerInput prfSeed seed message

/-- **A fresh answer truncates to a fixed digest with probability `2 ^ -128`.** -/
theorem prob_truncate_eq (target : Digest) :
    Pr{let answer ← ($ᵗ HashOutput : ProbComp HashOutput)}[Hashing.truncate answer = target] =
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hmap : Pr{let answer ← ($ᵗ HashOutput : ProbComp HashOutput)}[
        Hashing.truncate answer = target] =
      Pr{let digest ← (Hashing.truncate <$> ($ᵗ HashOutput : ProbComp HashOutput))}[
        digest = target] := by
    rw [prEvent_map]
  let _ : MeasurableSpace Digest := ⊤
  rw [hmap, KeygenUniform.truncate_uniform.prEvent_eq, prEvent_eq_evalDist_singleton,
    SampleableType.evalDist_uniformSample, ProbabilityTheory.uniformOn_univ_apply_singleton,
    Fintype.card_bitVec, one_div]
  rfl

end SlhDsaSecurity.RandomizerGate
