/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.PRFDerived.Retry

/-!
# Shared-response PRF-derived GXMSS

Three disjoint input families derive the public parameter, chain starts and retry randomizers
from one evaluator. A mapped first-success result retains attempts, consumed prefixes and failure.
-/

public section
namespace GXMSS.PRFDerived
open IncomparableEncoding GXMSS VCVio.Algorithms
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- A signing call consumes its epoch even on returned exhaustion. -/
structure SigningTransition (M R H : Type) (h v : ℕ) where
  /-- The supplied and consumed epoch. -/
  epoch : Fin (2 ^ h)
  /-- The signed message. -/
  message : M
  /-- Success or returned exhaustion with attempt evidence. -/
  result : SignResult R H h v

namespace SigningTransition

/-- Observe returned failure while retaining the consumed epoch in the transition. -/
@[expose] def output (transition : SigningTransition M R H h v) :
    Option (Signature R H h v) :=
  let signingResult := transition.result
  signingResult.output

/-- Observe the exact message/signature pair when signing succeeds. -/
@[expose] def messageSignature (transition : SigningTransition M R H h v) :
    Option (M × Signature R H h v) :=
  let output := transition.output
  output.map fun signature => (transition.message, signature)

end SigningTransition

/-- The returned secret key is exactly the sampled evaluator key. -/
abbrev SecretKey (Key : Type) := Key

/-- Assemble the public root from transient starts and endpoints.
Only the evaluator key is retained. -/
@[expose] def keys (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) :
    PublicKey PP H × SecretKey Key :=
  let pp := publicSeed evaluate interpretation key
  let starts := starts evaluate interpretation key pp
  let pair := GXMSS.keys hash pp starts
  (pair.1, key)

/-- The exact Construction 3 key assembly with a seed-only secret key. -/
theorem keys_eq (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) :
    keys hash evaluate interpretation key =
      let pp := interpretation.publicParameter (evaluate key .publicSeed)
      let starts := fun epoch chain =>
        interpretation.chainStart (evaluate key (.start pp epoch chain))
      ((GXMSS.keys hash pp starts).1, key) := rfl

/-- The public key exposes the parameter returned by `publicSeed`. -/
theorem keys_public_seed (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) :
    let pk := (keys hash evaluate interpretation key).1
    pk.seed = interpretation.publicParameter (evaluate key .publicSeed) := rfl

/-- The public root uses the same parameter and all derived chain endpoints. -/
theorem keys_root (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) :
    let pk := (keys hash evaluate interpretation key).1
    pk.root =
      let pp := interpretation.publicParameter (evaluate key .publicSeed)
      hash.merkleRoot pp (GXMSS.endpoints hash pp
        (fun epoch chain =>
          interpretation.chainStart (evaluate key (.start pp epoch chain)))) := rfl

/-- No chain start, endpoint, or authentication path is retained in the secret key. -/
theorem keys_secret_key (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) :
    (keys hash evaluate interpretation key).2 = key := rfl

/-- The transient Construction 3 key recomputes starts and endpoints from the evaluator key. -/
@[expose] def transientCore (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) :
    GXMSS.SecretKey PP H h v :=
  let pp := publicSeed evaluate interpretation key
  let starts := starts evaluate interpretation key pp
  let pair := GXMSS.keys hash pp starts
  pair.2

/-- A selected transient start is queried under the derived public parameter. -/
theorem transientCore_start (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    (transientCore hash evaluate interpretation key).starts epoch chain =
      let pp := interpretation.publicParameter (evaluate key .publicSeed)
      interpretation.chainStart (evaluate key (.start pp epoch chain)) := rfl

/-- A selected transient endpoint follows the Construction 3 chain under that parameter. -/
theorem transientCore_endpoint (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    (transientCore hash evaluate interpretation key).endpoints epoch chain =
      let pp := interpretation.publicParameter (evaluate key .publicSeed)
      hash.chain pp epoch chain 0 (2 ^ w - 1)
        (interpretation.chainStart (evaluate key (.start pp epoch chain))) := rfl

/-- Sample one key from the captured generator, then derive the public parameter and all starts. -/
@[expose] def keygen (sampleKey : ProbComp Key) (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) :
    ProbComp (PublicKey PP H × SecretKey Key) := do
  let key ← sampleKey
  pure (keys hash evaluate interpretation key)

/-- Key generation uses the captured evaluator-key sampler without a separate seed draw. -/
theorem keygen_eq (sampleKey : ProbComp Key) (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) :
    keygen sampleKey hash evaluate interpretation = (do
      let key ← sampleKey
      pure (keys hash evaluate interpretation key)) := rfl

/-- Deterministic first-success signing with a transient Construction 3 key. -/
@[expose] def run (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : SecretKey Key) (epoch : Fin (2 ^ h)) (message : M) :
    SigningTransition M R H h v :=
  let pp := publicSeed evaluate interpretation sk
  let core := transientCore hash evaluate interpretation sk
  let randomizers := retryRandomizers budget evaluate interpretation sk pp epoch message
  ⟨epoch, message, signResult hash enc core epoch message randomizers⟩

/-- Signing derives its starts, endpoints, and ordered retries from the same key and parameter. -/
theorem run_eq (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : SecretKey Key) (epoch : Fin (2 ^ h)) (message : M) :
    run budget evaluate interpretation hash enc sk epoch message =
      let pp := interpretation.publicParameter (evaluate sk .publicSeed)
      let starts := fun ep chain => interpretation.chainStart (evaluate sk (.start pp ep chain))
      let core := GXMSS.SecretKey.mk pp starts (GXMSS.endpoints hash pp starts)
      let randomizers := List.ofFn fun attempt : Fin budget =>
        interpretation.retryRandomizer (evaluate sk (.retry pp epoch message attempt.val))
      ⟨epoch, message,
        signResult hash enc core epoch message randomizers⟩ := rfl

/-- Signing with a generated key uses that key and the derived public parameter. -/
theorem run_keys_eq (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (key : Key) (epoch : Fin (2 ^ h)) (message : M) :
    run budget evaluate interpretation hash enc
        (keys hash evaluate interpretation key).2 epoch message =
      let pp := interpretation.publicParameter (evaluate key .publicSeed)
      let starts := fun ep chain => interpretation.chainStart (evaluate key (.start pp ep chain))
      let core := GXMSS.SecretKey.mk pp starts (GXMSS.endpoints hash pp starts)
      let randomizers := List.ofFn fun attempt : Fin budget =>
        interpretation.retryRandomizer (evaluate key (.retry pp epoch message attempt.val))
      ⟨epoch, message,
        signResult hash enc core epoch message randomizers⟩ := rfl

/-- The transition records the supplied epoch even when signing exhausts its budget. -/
theorem run_epoch (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : SecretKey Key) (epoch : Fin (2 ^ h)) (message : M) :
    (run budget evaluate interpretation hash enc sk epoch message).epoch = epoch := rfl

/-- Successful output is observed with the exact message supplied to this transition. -/
theorem run_messageSignature_eq (budget : ℕ)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : SecretKey Key) (epoch : Fin (2 ^ h)) (message : M) :
    let transition := run budget evaluate interpretation hash enc sk epoch message
    transition.messageSignature =
      Option.map (fun signature => (message, signature)) transition.output := rfl

/-- The deterministic returned-output observation retains exhaustion as `none`. -/
@[expose] def sign (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : SecretKey Key) (epoch : Fin (2 ^ h)) (message : M) :
    ProbComp (Option (Signature R H h v)) :=
  pure (run budget evaluate interpretation hash enc sk epoch message).output

/-- Signing observes exactly the first-success transition, including returned exhaustion. -/
theorem sign_eq (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : SecretKey Key) (epoch : Fin (2 ^ h)) (message : M) :
    sign budget evaluate interpretation hash enc sk epoch message =
      pure (run budget evaluate interpretation hash enc sk epoch message).output := rfl

/-- A zero retry budget returns exhaustion with an empty consumed sequence. -/
theorem run_zero (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : SecretKey Key) (epoch : Fin (2 ^ h)) (message : M) :
    run 0 evaluate interpretation hash enc sk epoch message =
      ⟨epoch, message, .exhausted []⟩ := rfl

/-- Verification uses the Construction 3 verifier with the public key's parameter. -/
@[expose] def verify [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (pk : PublicKey PP H) (epoch : Fin (2 ^ h)) (message : M)
    (signature : Signature R H h v) : Bool :=
  GXMSS.verify hash enc pk epoch message signature

/-- The exact verifier equation. -/
theorem verify_eq [DecidableEq H] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (pk : PublicKey PP H) (epoch : Fin (2 ^ h)) (message : M)
    (signature : Signature R H h v) :
    verify hash enc pk epoch message signature =
      GXMSS.verify hash enc pk epoch message signature := rfl

/-- Shared-seed derived GXMSS with the hash, arbitrary encoding, evaluator, and budget captured. -/
@[expose] def scheme [DecidableEq H]
    (sampleKey : ProbComp Key)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (budget : ℕ) :
    SyncSignatureAlg ProbComp M (PublicKey PP H) (SecretKey Key)
      (Signature R H h v) (Fin (2 ^ h)) where
  keygen := keygen sampleKey hash evaluate interpretation
  sign := sign budget evaluate interpretation hash enc
  verify := verify hash enc

end GXMSS.PRFDerived
