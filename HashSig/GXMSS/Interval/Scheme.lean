/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Merkle
import all HashSig.GXMSS.Interval.Merkle
public import HashSig.GXMSS.Scheme
import all HashSig.GXMSS.Scheme

/-!
# Generalized XMSS with an active epoch interval

The constructor captures an inclusive active interval before sampling keys. A complete secret
start and endpoint array remains available, while the public root and honest paths use independent
fillers at maximal inactive subtree roots. Verification is defined for every epoch in `Fin (2 ^ h)`,
including epochs outside the signing interval.
-/

public section

namespace GXMSS.Interval

open GXMSS.IntervalMerkle Encoding

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Number of active epoch, chain and positive-position coordinates. -/
@[expose] def activeChainPositionCount (I : Interval h) (w v : ℕ) : ℕ :=
  ((I.last : ℕ) - (I.first : ℕ) + 1) * v * (2 ^ w - 1)

/-- Full-range active chain coordinates retain the exact positive-position factor. -/
@[simp] theorem activeChainPositionCount_full (h w v : ℕ) :
    activeChainPositionCount (Interval.full h) w v = 2 ^ h * v * (2 ^ w - 1) := by
  have hn : 0 < 2 ^ h := by positivity
  simp only [activeChainPositionCount, Interval.full, Fin.val_zero]
  congr 2
  omega

/-- Complete GXMSS secret material together with the sampled inactive frontier. -/
structure SecretKey (PP H : Type) (h v : ℕ) (I : Interval h) where
  /-- Complete starts and stored endpoints. -/
  complete : GXMSS.SecretKey PP H h v
  /-- Uniform roots of maximal inactive subtrees. -/
  fillers : Fillers I H

/-- Forget only the inactive frontier table. -/
@[expose] def projectSecret {I : Interval h} (sk : SecretKey PP H h v I) :
    GXMSS.SecretKey PP H h v := sk.complete

/-- Assemble a mixed-tree public key from a full start array and frontier table. -/
@[expose] def keys (hash : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) :
    GXMSS.PublicKey PP H × SecretKey PP H h v I :=
  let complete := (GXMSS.keys hash pp starts).2
  (⟨GXMSS.IntervalMerkle.root hash I pp complete.endpoints fillers, pp⟩,
    ⟨complete, fillers⟩)

/-- Sample a public seed, all chain starts, and an independent root at each frontier node. -/
@[expose] noncomputable def keygen [SampleableType H] (hash : HashInstance PP T X H h w v)
    (I : Interval h) : ProbComp (GXMSS.PublicKey PP H × SecretKey PP H h v I) := do
  let pp ← (HashInstance.thf hash).seedGen
  let starts ← GXMSS.sampleStarts H h v
  let fillers ← GXMSS.IntervalMerkle.sampleFillers I H
  pure (keys hash I pp starts fillers)

/-- Honest signature data use the mixed-tree path and ordinary OTS prefix chains. -/
@[expose] def signatureOfWord (hash : HashInstance PP T X H h w v)
    (I : Interval h) (sk : SecretKey PP H h v I) (ep : Fin (2 ^ h))
    (wr : Encoding.Codeword v (2 ^ w) × R) : GXMSS.Signature R H h v :=
  let complete := sk.complete
  { GXMSS.signatureOfWord hash complete ep wr with
    path := GXMSS.IntervalMerkle.authPath hash I complete.seed complete.endpoints sk.fillers ep }

/-- Outside the selected interval, signing returns failure before any retry attempt. -/
@[expose] def sign [SampleableType R] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (sk : SecretKey PP H h v I) (ep : Fin (2 ^ h)) (msg : M) :
    ProbComp (Option (GXMSS.Signature R H h v)) :=
  let complete := sk.complete
  if Epoch.IsActive I ep then
    Option.map (signatureOfWord hash I sk ep) <$> enc.retry ($ᵗ R) complete.seed msg ep K
  else pure none

/-- Every epoch, including inactive epochs, is checked by `GXMSS.verify`. -/
@[expose] def verify [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (pk : GXMSS.PublicKey PP H) (ep : Fin (2 ^ h)) (msg : M)
    (sig : GXMSS.Signature R H h v) : Bool :=
  GXMSS.verify hash enc pk ep msg sig

/-- Captured hash, encoding, retry budget and interval define a synchronized signature scheme. -/
@[expose] noncomputable def scheme [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h) :
    SyncSignatureAlg ProbComp M (GXMSS.PublicKey PP H) (SecretKey PP H h v I)
      (GXMSS.Signature R H h v) (Fin (2 ^ h)) where
  keygen := keygen hash I
  sign := sign hash enc K I
  verify := verify hash enc

/-- Inactive signing fails as a returned result without sampling a randomizer. -/
theorem sign_not_isActive [SampleableType R] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (sk : SecretKey PP H h v I) (ep : Fin (2 ^ h)) (msg : M)
    (he : ¬ Epoch.IsActive I ep) : sign hash enc K I sk ep msg = pure none := by
  simp [sign, he]

/-- Generated-key equations for complete starts, stored endpoints, seed and mixed public root. -/
@[expose] def Consistent (hash : HashInstance PP T X H h w v) (I : Interval h)
    (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H h v I) : Prop :=
  let complete := sk.complete
  pk.seed = complete.seed ∧
    complete.endpoints = GXMSS.endpoints hash complete.seed complete.starts ∧
    pk.root = GXMSS.IntervalMerkle.root hash I complete.seed complete.endpoints sk.fillers

/-- Deterministic interval key assembly satisfies all generated-key equations. -/
theorem consistent_keys (hash : HashInstance PP T X H h w v) (I : Interval h)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) :
    Consistent hash I (keys hash I pp starts fillers).1
      (keys hash I pp starts fillers).2 := by
  simp [Consistent, keys, GXMSS.keys]

/-- Every active successful encoding produces a signature accepted by unrestricted verification. -/
theorem verify_signatureOfWord_isActive [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (I : Interval h) (pk : GXMSS.PublicKey PP H) (sk : SecretKey PP H h v I)
    (hc : Consistent hash I pk sk) (ep : Fin (2 ^ h)) (he : Epoch.IsActive I ep)
    (msg : M) (wr : Encoding.Codeword v (2 ^ w) × R)
    (hw : let complete := sk.complete
      enc.value complete.seed msg wr.2 ep = some wr.1) :
    verify hash enc pk ep msg (signatureOfWord hash I sk ep wr) = true := by
  let complete := sk.complete
  rcases hc with ⟨hseed, hend, hroot⟩
  have hchains : (fun i => hash.chain complete.seed ep i (wr.1 i)
      (2 ^ w - 1 - (wr.1 i).val)
      (hash.chain complete.seed ep i 0 (wr.1 i) (complete.starts ep i))) =
        complete.endpoints ep := by
    funext i
    rw [hash.chain_complete_digit, hend]
    rfl
  simp only [verify, GXMSS.verify, signatureOfWord, GXMSS.signatureOfWord,
    hseed, hw]
  rw [hchains, GXMSS.IntervalMerkle.recoverRoot_authPath_isActive hash I
    complete.seed complete.endpoints sk.fillers ep he, hroot]
  simp [complete]

/-- `verify` agrees with `GXMSS.verify` at every epoch, including inactive epochs. -/
theorem verify_eq_base [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (pk : GXMSS.PublicKey PP H) (ep : Fin (2 ^ h)) (msg : M)
    (sig : GXMSS.Signature R H h v) :
    verify hash enc pk ep msg sig = GXMSS.verify hash enc pk ep msg sig := rfl

/-- Projecting the empty frontier table from full-range `keys` gives `GXMSS.keys`, with the
same public seed, starts, endpoints and complete Merkle root. -/
theorem keys_full_project (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H)
    (fillers : Fillers (Interval.full h) H) :
    ((keys hash (Interval.full h) pp starts fillers).1,
      projectSecret (keys hash (Interval.full h) pp starts fillers).2) =
      GXMSS.keys hash pp starts := by
  simp [keys, projectSecret, GXMSS.keys, GXMSS.IntervalMerkle.root_full]

/-- At the full interval, `signatureOfWord` agrees with `GXMSS.signatureOfWord`, including
the `HashInstance.authPath` path and the OTS prefix chains. -/
theorem signatureOfWord_full (hash : HashInstance PP T X H h w v)
    (sk : SecretKey PP H h v (Interval.full h)) (ep : Fin (2 ^ h))
    (wr : Encoding.Codeword v (2 ^ w) × R) :
    signatureOfWord hash (Interval.full h) sk ep wr =
      GXMSS.signatureOfWord hash sk.complete ep wr := by
  simp [signatureOfWord, GXMSS.IntervalMerkle.authPath_full, GXMSS.signatureOfWord]

/-- At the full interval, `sign` agrees with `GXMSS.sign`, including returned retry failure. -/
theorem sign_full [SampleableType R] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (sk : SecretKey PP H h v (Interval.full h)) (ep : Fin (2 ^ h)) (msg : M) :
    sign hash enc K (Interval.full h) sk ep msg =
      GXMSS.sign hash enc K sk.complete ep msg := by
  simp only [sign, ite_eq_left (GXMSS.IntervalMerkle.Epoch.isActive_full ep), GXMSS.sign]
  congr 1
  funext o
  cases o with
  | none => rfl
  | some wr => simp [signatureOfWord_full]

/-- Full-range key generation agrees as a whole probabilistic computation after the
explicit secret projection; in particular its Boolean observations retain failure mass. -/
theorem keygen_full_project [SampleableType H]
    (hash : HashInstance PP T X H h w v) :
    (fun ks => (ks.1, projectSecret ks.2)) <$>
      keygen hash (Interval.full h) = GXMSS.keygen hash := by
  simp [keygen, GXMSS.keygen, GXMSS.IntervalMerkle.sampleFillers_full,
    keys_full_project, monad_norm]

end GXMSS.Interval
