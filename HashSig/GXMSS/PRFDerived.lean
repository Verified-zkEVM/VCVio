/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Scheme
public import HashSig.GXMSS.Encoding.RetryIndexed

/-!
# PRF-derived generalized XMSS

One sampled evaluator key supplies the public parameter, chain starts, and bounded signing
randomizers through distinct typed queries. The parameter derived at `publicSeed` is included in
every other query and is used throughout Construction 3. This is a deterministic specification of
the evaluator's use; it asserts no PRF advantage bound or comparison with independent sampling.
-/

public section

namespace GXMSS.PRFDerived

open Encoding GXMSS

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- The three disjoint query families for one shared evaluator key. -/
inductive Query (PP M : Type) (h v : ℕ) where
  /-- The public parameter from the distinguished query. -/
  | publicSeed
  /-- A chain start indexed by the derived parameter, epoch, and chain label. -/
  | start (pp : PP) (epoch : Fin (2 ^ h)) (chain : Fin v)
  /-- A retry randomizer indexed by the parameter, epoch, message, and zero-based attempt. -/
  | retry (pp : PP) (epoch : Fin (2 ^ h)) (message : M) (attempt : ℕ)

/-- A single abstract response domain for the shared keyed evaluator. -/
abbrev Evaluator (Key PP M Response : Type) (h v : ℕ) :=
  Key → Query PP M h v → Response

/-- Interpret the common response domain at each of the three disjoint query families. -/
structure Interpretation (PP H R Response : Type) where
  /-- Interpret the distinguished public-parameter response. -/
  publicParameter : Response → PP
  /-- Interpret a parameter-indexed chain-start response. -/
  chainStart : Response → H
  /-- Interpret a parameter-indexed retry response. -/
  retryRandomizer : Response → R

/-- The distinguished public-parameter query is separate from start queries. -/
theorem publicSeed_ne_start (pp : PP) (epoch : Fin (2 ^ h)) (chain : Fin v) :
    (Query.publicSeed : Query PP M h v) ≠ Query.start pp epoch chain := by
  intro equality
  cases equality

/-- The distinguished public-parameter query is separate from retry queries. -/
theorem publicSeed_ne_retry (pp : PP) (epoch : Fin (2 ^ h)) (message : M)
    (attempt : ℕ) :
    (Query.publicSeed : Query PP M h v) ≠ Query.retry pp epoch message attempt := by
  intro equality
  cases equality

/-- Start and retry queries are disjoint, including at the same public parameter. -/
theorem start_ne_retry (startPP : PP) (startEpoch : Fin (2 ^ h)) (chain : Fin v)
    (retryPP : PP) (retryEpoch : Fin (2 ^ h)) (message : M) (attempt : ℕ) :
    (Query.start startPP startEpoch chain : Query PP M h v) ≠
      Query.retry retryPP retryEpoch message attempt := by
  intro equality
  cases equality

/-- Equality of start queries determines their parameter, epoch, and chain label. -/
theorem start_eq_iff (pp₁ pp₂ : PP) (epoch₁ epoch₂ : Fin (2 ^ h))
    (chain₁ chain₂ : Fin v) :
    (Query.start pp₁ epoch₁ chain₁ : Query PP M h v) = Query.start pp₂ epoch₂ chain₂ ↔
      pp₁ = pp₂ ∧ epoch₁ = epoch₂ ∧ chain₁ = chain₂ := by
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Equality of retry queries determines every field, including the public parameter. -/
theorem retry_eq_iff (pp₁ pp₂ : PP) (epoch₁ epoch₂ : Fin (2 ^ h))
    (message₁ message₂ : M) (attempt₁ attempt₂ : ℕ) :
    (Query.retry pp₁ epoch₁ message₁ attempt₁ : Query PP M h v) =
        Query.retry pp₂ epoch₂ message₂ attempt₂ ↔
      pp₁ = pp₂ ∧ epoch₁ = epoch₂ ∧ message₁ = message₂ ∧ attempt₁ = attempt₂ := by
  constructor
  · intro equality
    cases equality
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- The public parameter derived from the sampled evaluator key. -/
@[expose] def publicSeed (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) : PP :=
  interpretation.publicParameter (evaluate key .publicSeed)

/-- All starts use the derived public parameter in their exact indexed queries. -/
@[expose] def starts (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) (pp : PP) :
    Fin (2 ^ h) → Fin v → H :=
  fun epoch chain => interpretation.chainStart (evaluate key (.start pp epoch chain))

/-- The query equation for a selected chain start. -/
theorem starts_apply (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (key : Key) (pp : PP)
    (epoch : Fin (2 ^ h)) (chain : Fin v) :
    starts evaluate interpretation key pp epoch chain =
      interpretation.chainStart (evaluate key (.start pp epoch chain)) := rfl

/-- The ordered randomizers for attempts `0, ..., budget - 1`. -/
@[expose] def retryRandomizers (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (key : Key) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) : List R :=
  List.ofFn fun attempt : Fin budget =>
    interpretation.retryRandomizer (evaluate key (.retry pp epoch message attempt.val))

/-- The derived retry sequence has exactly the requested budget. -/
theorem retryRandomizers_length (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (key : Key) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    (retryRandomizers budget evaluate interpretation key pp epoch message).length = budget :=
  List.length_ofFn

/-- Position `attempt` uses its exact zero-based PP-indexed query. -/
theorem retryRandomizers_get (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (key : Key) (pp : PP) (epoch : Fin (2 ^ h)) (message : M)
    (attempt : Fin budget) :
    (retryRandomizers budget evaluate interpretation key pp epoch message).get
        (Fin.cast
          (retryRandomizers_length budget evaluate interpretation key pp epoch message).symm
          attempt) =
      interpretation.retryRandomizer (evaluate key (.retry pp epoch message attempt.val)) := by
  simp [retryRandomizers, Fin.cast]

/-- First successful signature with its one-based attempt and ordered consumed prefix,
or returned exhaustion with the complete consumed list. -/
inductive SignResult (R H : Type) (h v : ℕ) where
  | success (signature : Signature R H h v) (attempt : ℕ) (consumed : List R)
  | exhausted (consumed : List R)

namespace SignResult

/-- Observe the returned signature or returned failure. -/
@[expose] def output : SignResult R H h v → Option (Signature R H h v)
  | .success signature _ _ => some signature
  | .exhausted _ => none

/-- Observe the first successful one-based attempt. -/
@[expose] def successfulAttempt : SignResult R H h v → Option ℕ
  | .success _ attempt _ => some attempt
  | .exhausted _ => none

/-- Observe the exact ordered consumed prefix. -/
@[expose] def consumed : SignResult R H h v → List R
  | .success _ _ randomizers => randomizers
  | .exhausted randomizers => randomizers

/-- Distinguish complete exhaustion from successful output. -/
@[expose] def isExhausted : SignResult R H h v → Bool
  | .success _ _ _ => false
  | .exhausted _ => true

end SignResult

/-- Deterministic signing uses the shared indexed first-success operation on the
finite derived retry sequence. Each finite index selects its exact randomizer. -/
@[expose] def signResult (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M)
    (randomizers : List R) : SignResult R H h v :=
  let sample : Fin randomizers.length → Id R := fun attempt => randomizers.get attempt
  match enc.retryIndexed sk.seed message epoch randomizers.length sample with
  | .success word randomizer attempt consumed =>
      .success (GXMSS.signatureOfWord hash sk epoch (word, randomizer))
        attempt consumed
  | .exhausted consumed => .exhausted consumed

/-- The empty derived sequence returns exhaustion without consumption. -/
theorem signResult_nil (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M) :
    signResult hash enc sk epoch message [] = .exhausted [] := rfl

/-- The indexed operation retains the familiar first-success list equation. -/
theorem signResult_cons (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M)
    (randomizer : R) (remaining : List R) :
    signResult hash enc sk epoch message (randomizer :: remaining) =
      match enc.value sk.seed message randomizer epoch with
      | some word => .success (GXMSS.signatureOfWord hash sk epoch (word, randomizer))
          1 [randomizer]
      | none =>
          match signResult hash enc sk epoch message remaining with
          | .success signature attempt consumed =>
              .success signature (attempt + 1) (randomizer :: consumed)
          | .exhausted consumed => .exhausted (randomizer :: consumed) := by
  simp only [signResult, List.length_cons, IncomparableEncoding.retryIndexed_id_succ,
    List.get_cons_zero]
  cases hv : enc.value sk.seed message randomizer epoch with
  | some word => simp
  | none =>
      cases htail : enc.retryIndexed (m := Id) sk.seed message epoch remaining.length
          (fun attempt => (remaining.get attempt : Id R))
      all_goals simp only [List.get_eq_getElem] at htail
      all_goals simp [htail]

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

/-- Sample one evaluator key, then derive the public parameter and all starts from it. -/
@[expose] def keygen [SampleableType Key] (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) :
    ProbComp (PublicKey PP H × SecretKey Key) := do
  let key ← $ᵗ Key
  pure (keys hash evaluate interpretation key)

/-- Key generation has exactly one evaluator-key sample and no separate seed draw. -/
theorem keygen_eq [SampleableType Key] (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) :
    keygen hash evaluate interpretation = (do
      let key ← $ᵗ Key
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
@[expose] def scheme [SampleableType Key] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response) (budget : ℕ) :
    SyncSignatureAlg ProbComp M (PublicKey PP H) (SecretKey Key)
      (Signature R H h v) (Fin (2 ^ h)) where
  keygen := keygen hash evaluate interpretation
  sign := sign budget evaluate interpretation hash enc
  verify := verify hash enc

end GXMSS.PRFDerived
