/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import VCVio.CryptoFoundations.SyncSignatureAlg.Security
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum


/-!
# Source games and observations

Internal Games 1–4 for Theorem 1 in ePrint 2025/055 use explicit Boolean observations.
The observations retain successful, unused and failed-consumed histories at the forged epoch.
The Game 3 to Game 4 partition charges only successful-record second-chain differences.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

/-- The finite set of signing epochs at tree height `h`. -/
abbrev Epoch (h : ℕ) := Fin (2 ^ h)

/-- A synchronized signature adversary for the generalized XMSS scheme. -/
abbrev SchemeAdversary (PP H M R : Type) (h v : ℕ) :=
  SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M
    (GXMSS.Signature R H h v)

/-- Complete internal result, including secret data unavailable to the source adversary. -/
structure Result (PP H M R : Type) (h v : ℕ) where
  /-- The public key supplied to the adversary. -/
  pk : GXMSS.PublicKey PP H
  /-- The secret key retained by the game. -/
  sk : GXMSS.SecretKey PP H h v
  /-- The adversary's final epoch, message and signature. -/
  forgery : SyncSignatureUnforgeability.Forgery (Epoch h) M (GXMSS.Signature R H h v)
  /-- Signing queries and their answers, indexed by epoch. -/
  history : SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v)

/-- Run the adopted source adversary with fixed generated keys and the accepted signing handler. -/
def runWithKeys [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v) :
    ProbComp (Result PP H M R h v) := do
  let alg := GXMSS.scheme hash enc K
  let impl : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      SyncSignatureUnforgeability.signingOracle alg sk
  let (forgery, history) ←
    (simulateQ impl (adv.forge pk)).run SyncSignatureUnforgeability.emptyHistory
  return ⟨pk, sk, forgery, history⟩

/-- A successfully returned honest signature retains a randomizer that encodes its message. -/
private theorem encoding_of_successful_sign [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) (ep : Epoch h) (msg : M)
    (sig : GXMSS.Signature R H h v)
    (hs : some sig ∈ support (GXMSS.sign hash enc K sk ep msg)) :
    ∃ word, enc.value sk.seed msg sig.randomizer ep = some word := by
  simp only [GXMSS.sign, support_map, Set.mem_image] at hs
  obtain ⟨answer, hanswer, heq⟩ := hs
  cases answer with
  | none => simp at heq
  | some wr =>
    have hsig : GXMSS.signatureOfWord hash sk ep wr = sig := by simpa using heq
    refine ⟨wr.1, ?_⟩
    rw [← hsig]
    exact IncomparableEncoding.Retry.value_eq_some_of_mem_retry enc
      ($ᵗ R) sk.seed msg ep K wr.1 wr.2 hanswer

/-- Every successful first signing record in a history has a valid encoding witness. -/
private def successfulHistoryEncodes
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) : Prop :=
  ∀ ep msg sig, history ep = some (msg, some sig) →
    ∃ wr, sig = GXMSS.signatureOfWord hash sk ep wr ∧
      enc.value sk.seed msg wr.2 ep = some wr.1

/-- The accepted signing handler preserves encoding witnesses for every successful record. -/
private theorem signingOracle_preserves_successfulHistoryEncodes
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) (q : Epoch h × M)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (hinv : successfulHistoryEncodes hash enc sk history)
    (out : Option (GXMSS.Signature R H h v) ×
      SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v))
    (hout : out ∈ support
      ((SyncSignatureUnforgeability.signingOracle (GXMSS.scheme hash enc K) sk q).run
        history)) :
    successfulHistoryEncodes hash enc sk out.2 := by
  rcases q with ⟨ep, msg⟩
  change out ∈ support
    (SyncSignatureUnforgeability.signingOracle (GXMSS.scheme hash enc K) sk (ep, msg)
      history) at hout
  by_cases hused : history ep = none
  · rw [SyncSignatureUnforgeability.signingOracle_unused _ _ _ _ _ hused] at hout
    simp only [mem_support_bind_iff] at hout
    obtain ⟨answer, hanswer, hreturn⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hreturn
    subst out
    intro ep' msg' sig' hentry
    by_cases heq : ep' = ep
    · subst ep'
      cases answer with
      | none => simp [Function.update] at hentry
      | some sig =>
        have hpair : msg' = msg ∧ sig' = sig := by
          simpa [Function.update] using hentry.symm
        rcases hpair with ⟨hmsg, hsig⟩
        change some sig ∈ support (GXMSS.sign hash enc K sk ep msg) at hanswer
        simp only [GXMSS.sign, support_map, Set.mem_image] at hanswer
        obtain ⟨answer, hwr, hsig'⟩ := hanswer
        cases answer with
        | none => simp at hsig'
        | some wr =>
          have heq : GXMSS.signatureOfWord hash sk ep wr = sig := by simpa using hsig'
          refine ⟨wr, ?_, ?_⟩
          · simpa [hmsg, hsig] using heq.symm
          · simpa [hmsg, hsig] using
              IncomparableEncoding.Retry.value_eq_some_of_mem_retry enc
                ($ᵗ R) sk.seed msg ep K wr.1 wr.2 hwr
    · have hold : history ep' = some (msg', some sig') := by
        simpa [Function.update, heq] using hentry
      exact hinv ep' msg' sig' hold
  · obtain ⟨first, answer, hrecord⟩ :
        ∃ first answer, history ep = some (first, answer) := by
      cases h : history ep with
      | none => exact False.elim (hused h)
      | some pair => exact ⟨pair.1, pair.2, rfl⟩
    rw [SyncSignatureUnforgeability.signingOracle_used _ _ _ _ _ _ _ hrecord] at hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact hinv

/-- A successful record produced by the actual source interaction has an encoding witness. -/
theorem runWithKeys_successful_record_signature [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runWithKeys hash enc K adv pk sk))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ wr, sig = GXMSS.signatureOfWord hash sk ep wr ∧
      enc.value sk.seed msg wr.2 ep = some wr.1 := by
  let impl : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      SyncSignatureUnforgeability.signingOracle (GXMSS.scheme hash enc K) sk
  have hpres : QueryImpl.PreservesInv impl (successfulHistoryEncodes hash enc sk) := by
    intro q history hinv z hz
    cases q with
    | inl uniform =>
      simp only [impl, QueryImpl.add_apply_inl] at hz
      simp only [QueryImpl.liftTarget_apply] at hz
      change z ∈ support
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) uniform) >>= fun answer =>
          pure (answer, history)) at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨answer, _, hreturn⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      subst z
      exact hinv
    | inr signing =>
      simpa only [impl, QueryImpl.add_apply_inr] using
        (signingOracle_preserves_successfulHistoryEncodes hash enc K sk signing
          history hinv z hz)
  have hinit : successfulHistoryEncodes hash enc sk
      SyncSignatureUnforgeability.emptyHistory := by
    intro ep msg sig hentry
    simp [SyncSignatureUnforgeability.emptyHistory] at hentry
  simp only [runWithKeys, mem_support_bind_iff] at hout
  obtain ⟨pair, hpair, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  have hfinal := OracleComp.simulateQ_run_preservesInv impl
    (successfulHistoryEncodes hash enc sk) hpres (adv.forge pk)
    SyncSignatureUnforgeability.emptyHistory hinit pair
  exact hfinal (by simpa only [impl] using hpair) ep msg sig hrecord

/-- A successful source record has a valid codeword at its returned randomizer. -/
theorem runWithKeys_successful_record_encodes [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runWithKeys hash enc K adv pk sk))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ word, enc.value sk.seed msg sig.randomizer ep = some word := by
  obtain ⟨wr, hsig, hword⟩ := runWithKeys_successful_record_signature
    hash enc K adv pk sk out hout ep msg sig hrecord
  refine ⟨wr.1, ?_⟩
  simpa [hsig, GXMSS.signatureOfWord] using hword

/-- Running with fixed keys retains those keys in every returned internal result. -/
theorem runWithKeys_support_keys [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (pk : GXMSS.PublicKey PP H) (sk : GXMSS.SecretKey PP H h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (runWithKeys hash enc K adv pk sk)) :
    out.pk = pk ∧ out.sk = sk := by
  simp only [runWithKeys, mem_support_bind_iff] at hout
  obtain ⟨pair, _, hret⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hret
  subst out
  exact ⟨rfl, rfl⟩

/-- Honest key generation followed by the unchanged source interaction. -/
def sourceProgram [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ProbComp (Result PP H M R h v) := do
  let (pk, sk) ← GXMSS.keygen hash
  runWithKeys hash enc K adv pk sk

/-- Every returned source result retains the same public seed in both generated keys. -/
theorem sourceProgram_support_seed_eq [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv)) :
    let publicKey := out.pk
    let secretKey := out.sk
    publicKey.seed = secretKey.seed := by
  simp only [sourceProgram, mem_support_bind_iff] at hout
  obtain ⟨keys, hkeys, hrun⟩ := hout
  let generatedPublicKey := keys.1
  let generatedSecretKey := keys.2
  have hseeds : generatedPublicKey.seed = generatedSecretKey.seed := by
    simp only [GXMSS.keygen, mem_support_bind_iff] at hkeys
    obtain ⟨pp, _, hstarts⟩ := hkeys
    obtain ⟨starts, _, hret⟩ := hstarts
    simp only [support_pure, Set.mem_singleton_iff] at hret
    subst keys
    rfl
  obtain ⟨hpk, hsk⟩ := runWithKeys_support_keys hash enc K adv keys.1 keys.2 out hrun
  simpa only [generatedPublicKey, generatedSecretKey, hpk, hsk] using hseeds

/-- A returned successful source record is the honest chain-prefix signature of its retry word. -/
theorem sourceProgram_successful_record_signature [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ wr, sig = GXMSS.signatureOfWord hash out.sk ep wr ∧
      enc.value out.pk.seed msg wr.2 ep = some wr.1 := by
  simp only [sourceProgram, mem_support_bind_iff] at hout
  obtain ⟨keys, hkeys, hrun⟩ := hout
  have hseeds : keys.1.seed = keys.2.seed := by
    simp only [GXMSS.keygen, mem_support_bind_iff] at hkeys
    obtain ⟨pp, _, hstarts⟩ := hkeys
    obtain ⟨starts, _, hret⟩ := hstarts
    simp only [support_pure, Set.mem_singleton_iff] at hret
    subst keys
    rfl
  obtain ⟨hpk, hsk⟩ := runWithKeys_support_keys hash enc K adv keys.1 keys.2 out hrun
  obtain ⟨wr, hsig, hword⟩ := runWithKeys_successful_record_signature
    hash enc K adv keys.1 keys.2 out hrun ep msg sig hrecord
  exact ⟨wr, by simpa only [hsk] using hsig,
    by simpa only [hpk, hseeds] using hword⟩

/-- Every successful forged-epoch record in a returned source interaction has a successful
encoding at the public seed. -/
theorem sourceProgram_successful_record_encodes [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ word, enc.value out.pk.seed msg sig.randomizer ep = some word := by
  simp only [sourceProgram, mem_support_bind_iff] at hout
  obtain ⟨keys, hkeys, hrun⟩ := hout
  have hseeds : keys.1.seed = keys.2.seed := by
    simp only [GXMSS.keygen, mem_support_bind_iff] at hkeys
    obtain ⟨pp, _, hstarts⟩ := hkeys
    obtain ⟨starts, _, hret⟩ := hstarts
    simp only [support_pure, Set.mem_singleton_iff] at hret
    subst keys
    rfl
  obtain ⟨hpk, hsk⟩ := runWithKeys_support_keys hash enc K adv keys.1 keys.2 out hrun
  obtain ⟨word, hword⟩ := runWithKeys_successful_record_encodes
    hash enc K adv keys.1 keys.2 out hrun ep msg sig hrecord
  refine ⟨word, ?_⟩
  simpa only [hpk, hseeds] using hword

/-- Forget only the secret key added for internal game reasoning. -/
def sourceObservation (out : Result PP H M R h v) :
    SyncSignatureUnforgeability.ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v) :=
  (out.pk, out.forgery, out.history)

/-- The exact strong-unforgeability observation on an internal source result. -/
def sourceStrongObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  SyncSignatureUnforgeability.strongValid (GXMSS.scheme hash enc K) (sourceObservation out)

/-- The internal source program, observed without its secret key, is exactly the executable
strong-unforgeability interaction. -/
theorem sourceProgram_map_eq_interaction [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    sourceObservation <$> sourceProgram hash enc K adv =
    SyncSignatureUnforgeability.interaction (GXMSS.scheme hash enc K) adv := by
  simp [sourceProgram, runWithKeys, sourceObservation,
    SyncSignatureUnforgeability.interaction, GXMSS.scheme, map_eq_bind_pure_comp, bind_assoc]

/-- The exact successful-output measure of the executable source computation. -/
noncomputable def sourceStrongOutputMeasure [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : MeasureTheory.Measure Bool :=
  ProbCompRuntime.probComp.evalDist
    (sourceStrongObservation hash enc K <$> sourceProgram hash enc K adv)

/-- Observing the internal source program gives exactly the adopted executable strong-
unforgeability measure; the secret key is forgotten and no mass is conditioned away. -/
theorem sourceStrongOutputMeasure_eq_strongUnforgeableExp
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    sourceStrongOutputMeasure hash enc K adv =
      SyncSignatureUnforgeability.strongUnforgeableExp (GXMSS.scheme hash enc K)
        ProbCompRuntime.probComp adv := by
  simp only [sourceStrongOutputMeasure, SyncSignatureUnforgeability.strongUnforgeableExp,
    SyncSignatureUnforgeability.outputMeasure]
  congr 1
  change (fun out => SyncSignatureUnforgeability.strongValid
    (GXMSS.scheme hash enc K) (sourceObservation out)) <$> sourceProgram hash enc K adv = _
  rw [← Functor.map_map, sourceProgram_map_eq_interaction hash enc K adv]

/-- Exact source-history classification at the forged epoch. -/
inductive ForgedEpochSource (M S : Type)
  | unused
  | successful (message : M) (signature : S)
  | failedConsumed (message : M)

/-- Classify `none`, `some (msg, some signature)`, and `some (msg, none)` without merging cases. -/
def forgedEpochSource (out : Result PP H M R h v) :
    ForgedEpochSource M (GXMSS.Signature R H h v) :=
  let forgery := out.forgery
  match out.history forgery.1 with
  | none => .unused
  | some (msg, some signature) => .successful msg signature
  | some (msg, none) => .failedConsumed msg

/-- A successful source classification names the exact first-request history entry. -/
theorem history_of_successful_source (out : Result PP H M R h v)
    (msg : M) (sig : GXMSS.Signature R H h v)
    (hsource : forgedEpochSource out = .successful msg sig) :
    out.history out.forgery.1 = some (msg, some sig) := by
  unfold forgedEpochSource at hsource
  cases hentry : out.history out.forgery.1 with
  | none => simp [hentry] at hsource
  | some entry =>
    rcases entry with ⟨first, answer⟩
    cases answer with
    | none => simp [hentry] at hsource
    | some firstSig =>
      have hpair : first = msg ∧ firstSig = sig := by
        simpa [hentry] using hsource
      rcases hpair with ⟨rfl, rfl⟩
      rfl

/-- A fresh request with strict remaining room is never rejected by the reduction's
`qs`-record target transcript. -/
theorem encodingFreshQuery_capacity [DecidableEq E]
    (qs : ℕ) (s : TargetCollisionResistance.Transcript M R E n radix)
    (ep : E) (hlen : s.length < qs)
    (hfresh : TargetCollisionResistance.used s ep = false) :
    TargetCollisionResistance.rejected qs s ep = false := by
  simp [TargetCollisionResistance.rejected, hfresh, Nat.not_le.mpr hlen]

/-- Any previously consumed epoch, including a failed one, is rejected before sampling. -/
theorem encodingConsumedEpoch_rejected [DecidableEq E]
    (qs : ℕ) (s : TargetCollisionResistance.Transcript M R E n radix) (ep : E)
    (hused : TargetCollisionResistance.used s ep = true) :
    TargetCollisionResistance.rejected qs s ep = true := by
  exact TargetCollisionResistance.rejected_of_used _ _ _ hused

/-- The leaf recovered from the candidate signature, when its encoding succeeds. -/
def forgedLeaf? (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (out : Result PP H M R h v) : Option (Fin v → H) :=
  let publicKey := out.pk
  let forgery := out.forgery
  let forgedEpoch := forgery.1
  let forgedPayload := forgery.2
  let forgedMessage := forgedPayload.1
  let forgedSignature := forgedPayload.2
  (enc.value publicKey.seed forgedMessage forgedSignature.randomizer forgedEpoch).map
    fun word i => hash.chain publicKey.seed forgedEpoch i (word i)
      (2 ^ w - 1 - (word i).val) (forgedSignature.ots i)

/-- Game 1 keeps a strong source win only when complete honest and forged openings agree. -/
def gameOneObservation [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  let publicKey := out.pk
  let secretKey := out.sk
  let forgery := out.forgery
  let forgedEpoch := forgery.1
  let forgedPayload := forgery.2
  let forgedSignature := forgedPayload.2
  SyncSignatureUnforgeability.strongValid (GXMSS.scheme hash enc K)
      (publicKey, forgery, out.history) &&
    match forgedLeaf? hash enc out with
    | none => false
    | some leaf => decide ((secretKey.endpoints forgedEpoch,
        hash.authPath publicKey.seed secretKey.endpoints forgedEpoch) =
      (leaf, forgedSignature.path))

/-- The complementary source observation in which the complete honest and forged raw Merkle
openings differ.  This single pair comparison includes a raw-leaf difference, a path-only
difference, and height zero without requiring either component to differ in advance. -/
def merkleDifferenceObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  let publicKey := out.pk
  let secretKey := out.sk
  let forgery := out.forgery
  let forgedEpoch := forgery.1
  let forgedPayload := forgery.2
  let forgedSignature := forgedPayload.2
  sourceStrongObservation hash enc K out &&
    match forgedLeaf? hash enc out with
    | none => false
    | some leaf => decide ((secretKey.endpoints forgedEpoch,
        hash.authPath publicKey.seed secretKey.endpoints forgedEpoch) ≠
      (leaf, forgedSignature.path))

/-- The exact source winning observation partitions into Game 1 and unequal complete Merkle
openings.  It is a Boolean identity on returned results and therefore does not normalize missing
execution mass. -/
theorem sourceStrongObservation_eq_gameOne_or_merkleDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) :
    sourceStrongObservation hash enc K out =
      (gameOneObservation hash enc K out || merkleDifferenceObservation hash enc K out) := by
  simp only [sourceStrongObservation, sourceObservation, gameOneObservation,
    merkleDifferenceObservation, SyncSignatureUnforgeability.strongValid, GXMSS.scheme,
    GXMSS.verify]
  split <;> simp_all only [forgedLeaf?, Option.map_some, Prod.mk.injEq, Bool.decide_and,
    ne_eq, not_and, decide_implies, decide_not, dite_eq_ite, Bool.ite_true_right]
  · rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.or_eq_true]
    classical
    tauto
  · rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not]
    classical
    tauto

/-- Game 1 program; only its observation differs from the adopted source experiment. -/
def gameOne := @sourceProgram PP T X H M R h w v

/-- The exact post-runtime Boolean measure for Game 1.  Both returned outcomes and all missing
execution mass are inherited from the same partial source computation. -/
noncomputable def gameOneOutputMeasure [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : MeasureTheory.Measure Bool :=
  ProbCompRuntime.probComp.evalDist
    (gameOneObservation hash enc K <$> gameOne hash enc K adv)

/-- Game 1 winning mass is observed at the returned Boolean `true`, without conditioning. -/
noncomputable def gameOneAdvantage [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  gameOneOutputMeasure hash enc K adv {true}

/-- Game 2 removes an unequal-input/equal-codeword encoding collision only on a successful
record. -/
def gameTwoObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  let publicKey := out.pk
  let forgery := out.forgery
  let forgedEpoch := forgery.1
  let forgedPayload := forgery.2
  let forgedMessage := forgedPayload.1
  let forgedSignature := forgedPayload.2
  gameOneObservation hash enc K out &&
    match forgedEpochSource out with
    | .unused => true
    | .failedConsumed _ => true
    | .successful msg sig =>
        match enc.value publicKey.seed msg sig.randomizer forgedEpoch,
          enc.value publicKey.seed forgedMessage forgedSignature.randomizer forgedEpoch with
        | some honestWord, some forgedWord =>
            decide ((msg, sig.randomizer) =
              (forgedMessage, forgedSignature.randomizer) ∨ honestWord ≠ forgedWord)
        | _, _ => false

/-- Game 2 uses the same interaction and the encoding-collision-filtered observation. -/
def gameTwo := @sourceProgram PP T X H M R h w v

/-- The native Boolean output measure for Game 2, retaining returned failure and unreturned
mass from the source interaction. -/
noncomputable def gameTwoOutputMeasure [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : MeasureTheory.Measure Bool :=
  ProbCompRuntime.probComp.evalDist
    (gameTwoObservation hash enc K <$> gameTwo hash enc K adv)

/-- Game 2 winning mass is the unconditioned returned `true` measure. -/
noncomputable def gameTwoAdvantage [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  gameTwoOutputMeasure hash enc K adv {true}

/-- The successful-record part of the Game 1 to Game 2 observation difference.  The record
encodes to the forged word at the same epoch, but its message/randomizer pair is different. -/
def successfulEncodingDifference [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  gameOneObservation hash enc K out && !gameTwoObservation hash enc K out &&
    match forgedEpochSource out with
    | .successful _ _ => true
    | _ => false

/-- The native returned mass of the successful-record observation difference. -/
noncomputable def successfulEncodingDifferenceMass [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist
    (successfulEncodingDifference hash enc K <$> sourceProgram hash enc K adv) {true}

/-- Game 2 leaves an unused forged epoch's Game 1 observation unchanged. -/
theorem gameTwoObservation_unused [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (hsource : forgedEpochSource out = .unused) :
    gameTwoObservation hash enc K out = gameOneObservation hash enc K out := by
  simp [gameTwoObservation, hsource]

/-- Game 2 leaves a failed-but-consumed forged epoch's Game 1 observation unchanged. -/
theorem gameTwoObservation_failedConsumed [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (msg : M)
    (hsource : forgedEpochSource out = .failedConsumed msg) :
    gameTwoObservation hash enc K out = gameOneObservation hash enc K out := by
  simp [gameTwoObservation, hsource]

/-- On every returned source result, Game 1 is exactly the disjunction of Game 2 and the
successful-record difference.  Unused and failed-consumed forged epochs have zero difference. -/
theorem gameOneObservation_eq_gameTwo_or_successfulDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) :
    gameOneObservation hash enc K out =
      (gameTwoObservation hash enc K out ||
        successfulEncodingDifference hash enc K out) := by
  cases hs : forgedEpochSource out with
  | unused =>
    simp [gameTwoObservation, successfulEncodingDifference, hs]
  | failedConsumed msg =>
    simp [gameTwoObservation, successfulEncodingDifference, hs]
  | successful msg sig =>
    simp only [gameTwoObservation, successfulEncodingDifference, hs]
    cases gameOneObservation hash enc K out <;>
      cases (match enc.value out.pk.seed msg sig.randomizer out.forgery.1,
          enc.value out.pk.seed out.forgery.2.1 out.forgery.2.2.randomizer
            out.forgery.1 with
        | some honestWord, some forgedWord =>
            decide ((msg, sig.randomizer) =
              (out.forgery.2.1, out.forgery.2.2.randomizer) ∨
              honestWord ≠ forgedWord)
        | _, _ => false) <;> decide

/-- The native Game 1 winning mass is bounded by Game 2 plus only the returned
successful-record difference, without conditioning on source termination. -/
theorem gameOneAdvantage_le_gameTwo_add_successfulDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    gameOneAdvantage hash enc K adv ≤
      gameTwoAdvantage hash enc K adv +
        successfulEncodingDifferenceMass hash enc K adv := by
  simp only [gameOneAdvantage, gameOneOutputMeasure, gameOne,
    gameTwoAdvantage, gameTwoOutputMeasure, gameTwo,
    successfulEncodingDifferenceMass, ProbCompRuntime.probComp_evalDist,
    map_eq_bind_pure_comp]
  apply OracleComp.evalDist_bind_apply_le_add_of_support
    (sourceProgram hash enc K adv)
    (fun out => pure (gameOneObservation hash enc K out))
    (fun out => pure (gameTwoObservation hash enc K out))
    (fun out => pure (successfulEncodingDifference hash enc K out))
    (by measurability)
  intro out _
  rw [gameOneObservation_eq_gameTwo_or_successfulDifference hash enc K out]
  cases gameTwoObservation hash enc K out <;>
    cases successfulEncodingDifference hash enc K out <;>
    simp

/-- A returned Game 1 win has a successful forged encoding. -/
theorem forged_encoding_of_gameOne_win [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v)
    (hwin : gameOneObservation hash enc K out = true) :
    ∃ word, enc.value out.pk.seed out.forgery.2.1
      out.forgery.2.2.randomizer out.forgery.1 = some word := by
  cases hword : enc.value out.pk.seed out.forgery.2.1
      out.forgery.2.2.randomizer out.forgery.1 with
  | none =>
    simp [gameOneObservation, forgedLeaf?, hword] at hwin
  | some word => exact ⟨word, rfl⟩

/-- Game 1's complete-opening equality equates each honest endpoint with the forged chain
endpoint at its actual encoding digit. -/
theorem gameOneObservation_endpoint_eq_forged [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (word : Codeword v (2 ^ w))
    (hword : enc.value out.pk.seed out.forgery.2.1
      out.forgery.2.2.randomizer out.forgery.1 = some word)
    (hone : gameOneObservation hash enc K out = true) (i : Fin v) :
    out.sk.endpoints out.forgery.1 i =
      hash.chain out.pk.seed out.forgery.1 i (word i)
        (2 ^ w - 1 - (word i).val) (out.forgery.2.2.ots i) := by
  have hone' := hone
  simp only [gameOneObservation, Bool.and_eq_true] at hone'
  have hleaf : forgedLeaf? hash enc out =
      some (fun i => hash.chain out.pk.seed out.forgery.1 i (word i)
        (2 ^ w - 1 - (word i).val) (out.forgery.2.2.ots i)) := by
    simp [forgedLeaf?, hword]
  rw [hleaf] at hone'
  have hopen := of_decide_eq_true hone'.2
  exact congrArg (fun f => f i) (congrArg Prod.fst hopen)

/-- On a successful first record, a Game 1 win removed by Game 2 supplies exactly the
same-epoch, same-codeword, distinct-pair target-collision witness. -/
theorem successful_encoding_difference_witness [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (msg : M) (sig : GXMSS.Signature R H h v)
    (hsource : forgedEpochSource out = .successful msg sig)
    (hhonest : ∃ word, enc.value out.pk.seed msg sig.randomizer out.forgery.1 =
      some word)
    (hwin : gameOneObservation hash enc K out = true)
    (hremoved : gameTwoObservation hash enc K out = false) :
    ∃ word, enc.value out.pk.seed msg sig.randomizer out.forgery.1 = some word ∧
      enc.value out.pk.seed out.forgery.2.1 out.forgery.2.2.randomizer
        out.forgery.1 = some word ∧
      (msg, sig.randomizer) ≠ (out.forgery.2.1, out.forgery.2.2.randomizer) := by
  obtain ⟨honestWord, hhonestWord⟩ := hhonest
  obtain ⟨forgedWord, hforgedWord⟩ :=
    forged_encoding_of_gameOne_win hash enc K out hwin
  have hcheck := hremoved
  simp only [gameTwoObservation, hsource, hwin,
    hhonestWord, hforgedWord] at hcheck
  have hnot : ¬ ((msg, sig.randomizer) =
      (out.forgery.2.1, out.forgery.2.2.randomizer) ∨
      honestWord ≠ forgedWord) := by
    exact of_decide_eq_false hcheck
  have hword : honestWord = forgedWord := by
    by_contra h
    exact hnot (Or.inr h)
  refine ⟨honestWord, hhonestWord, ?_, ?_⟩
  · simpa only [hword] using hforgedWord
  · exact fun h => hnot (Or.inl h)

/-- The successful-record difference of a returned source execution has the exact
encoding target-collision witness, with no extra hypothesis on the adversary. -/
theorem successful_encoding_difference_source_witness [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv))
    (msg : M) (sig : GXMSS.Signature R H h v)
    (hsource : forgedEpochSource out = .successful msg sig)
    (hwin : gameOneObservation hash enc K out = true)
    (hremoved : gameTwoObservation hash enc K out = false) :
    ∃ word, enc.value out.pk.seed msg sig.randomizer out.forgery.1 = some word ∧
      enc.value out.pk.seed out.forgery.2.1 out.forgery.2.2.randomizer
        out.forgery.1 = some word ∧
      (msg, sig.randomizer) ≠ (out.forgery.2.1, out.forgery.2.2.randomizer) := by
  have hrecord := history_of_successful_source out msg sig hsource
  have hhonest := sourceProgram_successful_record_encodes hash enc K adv out hout
    out.forgery.1 msg sig hrecord
  exact successful_encoding_difference_witness hash enc K out msg sig
    hsource hhonest hwin hremoved

/-- A successful transcript entry with the forged word and a distinct input pair makes the
authoritative target-collision predicate true. -/
theorem encodingTargetValid_of_successful_record [DecidableEq M] [DecidableEq R]
    [DecidableEq E]
    (enc : IncomparableEncoding PP M R E n radix) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix)
    (ep : E) (targetMsg candidateMsg : M) (targetR candidateR : R)
    (word : Codeword n radix)
    (hrecord : (⟨ep, targetMsg, some (word, targetR)⟩ :
      TargetCollisionResistance.Record M R E n radix) ∈ transcript)
    (hvalue : enc.value pp candidateMsg candidateR ep = some word)
    (hne : (targetMsg, targetR) ≠ (candidateMsg, candidateR)) :
    TargetCollisionResistance.valid enc pp transcript (candidateMsg, candidateR, ep) =
      true := by
  simp only [TargetCollisionResistance.valid, hvalue]
  apply List.any_eq_true.mpr
  refine ⟨⟨ep, targetMsg, some (word, targetR)⟩, hrecord, ?_⟩
  simp [hne]

/-- Game 3 removes the equal-input, different-OTS chain-collision branch. -/
def gameThreeObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  let forgery := out.forgery
  let forgedPayload := forgery.2
  let forgedMessage := forgedPayload.1
  let forgedSignature := forgedPayload.2
  gameTwoObservation hash enc K out &&
    match forgedEpochSource out with
    | .successful msg sig => decide ((msg, sig.randomizer) ≠
        (forgedMessage, forgedSignature.randomizer) ∨ sig.ots = forgedSignature.ots)
    | _ => true

/-- Game 3 uses the first-chain-filtered observation. -/
def gameThree := @sourceProgram PP T X H M R h w v

/-- Game 3's native returned Boolean measure, with the source's false and missing mass intact. -/
noncomputable def gameThreeOutputMeasure [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : MeasureTheory.Measure Bool :=
  ProbCompRuntime.probComp.evalDist
    (gameThreeObservation hash enc K <$> gameThree hash enc K adv)

/-- Game 3's unconditioned returned winning mass. -/
noncomputable def gameThreeAdvantage [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  gameThreeOutputMeasure hash enc K adv {true}

/-- Game 3 only removes returned Game 2 wins on a successful forged-epoch record. -/
def successfulFirstChainDifference [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  gameTwoObservation hash enc K out && !gameThreeObservation hash enc K out &&
    match forgedEpochSource out with
    | .successful _ _ => true
    | _ => false

/-- Native returned mass removed by the first-chain filter. -/
noncomputable def successfulFirstChainDifferenceMass [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist
    (successfulFirstChainDifference hash enc K <$> sourceProgram hash enc K adv) {true}

/-- Unused forged epochs retain the Game 2 Boolean observation. -/
theorem gameThreeObservation_unused [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (hsource : forgedEpochSource out = .unused) :
    gameThreeObservation hash enc K out = gameTwoObservation hash enc K out := by
  simp [gameThreeObservation, hsource]

/-- Failed-but-consumed forged epochs retain the Game 2 Boolean observation. -/
theorem gameThreeObservation_failedConsumed [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (msg : M)
    (hsource : forgedEpochSource out = .failedConsumed msg) :
    gameThreeObservation hash enc K out = gameTwoObservation hash enc K out := by
  simp [gameThreeObservation, hsource]

/-- A Game 3 win with an honest path cannot reuse the honest codeword: equal randomizer/message
and OTS data would make the exact returned signature pair non-fresh. -/
theorem gameThree_successful_words_ne [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (msg : M) (sig : GXMSS.Signature R H h v)
    (honestWord forgedWord : Codeword v (2 ^ w))
    (hsource : forgedEpochSource out = .successful msg sig)
    (hthree : gameThreeObservation hash enc K out = true)
    (hhonest : enc.value out.pk.seed msg sig.randomizer out.forgery.1 = some honestWord)
    (hforged : enc.value out.pk.seed out.forgery.2.1
      out.forgery.2.2.randomizer out.forgery.1 = some forgedWord)
    (hpath : sig.path = out.forgery.2.2.path) : honestWord ≠ forgedWord := by
  intro hword
  have htwo : gameTwoObservation hash enc K out = true := by
    simp only [gameThreeObservation, Bool.and_eq_true] at hthree
    exact hthree.1
  have hone : gameOneObservation hash enc K out = true := by
    simp only [gameTwoObservation, Bool.and_eq_true] at htwo
    exact htwo.1
  have hpair : (msg, sig.randomizer) =
      (out.forgery.2.1, out.forgery.2.2.randomizer) := by
    have hcheck := htwo
    simp only [gameTwoObservation, hsource, hone, Bool.true_and,
      hhonest, hforged] at hcheck
    exact (of_decide_eq_true hcheck).resolve_right (by simp [hword])
  have hots : sig.ots = out.forgery.2.2.ots := by
    have hcheck := hthree
    simp only [gameThreeObservation, hsource, htwo, Bool.true_and] at hcheck
    exact (of_decide_eq_true hcheck).resolve_left (by simp [hpair])
  have hsig : sig = out.forgery.2.2 := by
    cases sig with
    | mk r ots path =>
      cases hf : out.forgery.2.2 with
      | mk r' ots' path' =>
        simp only [hf] at hpair hots hpath ⊢
        have hr : r = r' := congrArg Prod.snd hpair
        cases hr
        cases hots
        cases hpath
        rfl
  have hstrong : SyncSignatureUnforgeability.strongFresh out.history out.forgery = true := by
    have hw := hone
    simp only [gameOneObservation, Bool.and_eq_true] at hw
    have hs := hw.1
    simp only [SyncSignatureUnforgeability.strongValid, Bool.and_eq_true] at hs
    exact hs.2
  have hrecord := history_of_successful_source out msg sig hsource
  have hfresh : msg ≠ out.forgery.2.1 := by
    simpa [SyncSignatureUnforgeability.strongFresh, hrecord, hsig] using hstrong
  exact hfresh (congrArg Prod.fst hpair)

/-- Every returned Game 2 win is a Game 3 win or the successful first-chain difference. -/
theorem gameTwoObservation_eq_gameThree_or_successfulFirstChainDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) :
    gameTwoObservation hash enc K out =
      (gameThreeObservation hash enc K out ||
        successfulFirstChainDifference hash enc K out) := by
  cases hs : forgedEpochSource out with
  | unused => simp [gameThreeObservation, successfulFirstChainDifference, hs]
  | failedConsumed msg => simp [gameThreeObservation, successfulFirstChainDifference, hs]
  | successful msg sig =>
    simp only [gameThreeObservation, successfulFirstChainDifference, hs]
    cases gameTwoObservation hash enc K out <;>
      cases decide ((msg, sig.randomizer) ≠
        (out.forgery.2.1, out.forgery.2.2.randomizer) ∨
        sig.ots = out.forgery.2.2.ots) <;> decide

/-- The returned Game 2 winning mass is at most Game 3 plus the removed successful mass. -/
theorem gameTwoAdvantage_le_gameThree_add_successfulFirstChainDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    gameTwoAdvantage hash enc K adv ≤
      gameThreeAdvantage hash enc K adv +
        successfulFirstChainDifferenceMass hash enc K adv := by
  simp only [gameTwoAdvantage, gameTwoOutputMeasure, gameTwo,
    gameThreeAdvantage, gameThreeOutputMeasure, gameThree,
    successfulFirstChainDifferenceMass, ProbCompRuntime.probComp_evalDist,
    map_eq_bind_pure_comp]
  apply OracleComp.evalDist_bind_apply_le_add_of_support
    (sourceProgram hash enc K adv)
    (fun out => pure (gameTwoObservation hash enc K out))
    (fun out => pure (gameThreeObservation hash enc K out))
    (fun out => pure (successfulFirstChainDifference hash enc K out))
    (by measurability)
  intro out _
  rw [gameTwoObservation_eq_gameThree_or_successfulFirstChainDifference hash enc K out]
  cases gameThreeObservation hash enc K out <;>
    cases successfulFirstChainDifference hash enc K out <;> simp

/-- Equation (4)'s designated-cut equality, when both encodings and the smaller coordinate exist. -/
def designatedCutHolds [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (out : Result PP H M R h v) : Bool :=
  let publicKey := out.pk
  let forgery := out.forgery
  let forgedEpoch := forgery.1
  let forgedPayload := forgery.2
  let forgedMessage := forgedPayload.1
  let forgedSignature := forgedPayload.2
  match forgedEpochSource out with
  | .successful msg sig =>
      match enc.value publicKey.seed msg sig.randomizer forgedEpoch,
        enc.value publicKey.seed forgedMessage forgedSignature.randomizer forgedEpoch with
      | some honestWord, some forgedWord =>
          match findSmallerCoordinate honestWord forgedWord with
          | none => false
          | some i => decide (hash.chain publicKey.seed forgedEpoch i (forgedWord i)
              ((honestWord i).val - (forgedWord i).val) (forgedSignature.ots i) = sig.ots i)
      | _, _ => false
  | _ => true

/-- Game 4 additionally requires the designated later-chain equality. -/
def gameFourObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  gameThreeObservation hash enc K out && designatedCutHolds hash enc out

/-- Game 4 uses the second-chain-filtered observation. -/
def gameFour := @sourceProgram PP T X H M R h w v

/-- The native Game 4 Boolean measure retains both returned outcomes and missing mass. -/
noncomputable def gameFourOutputMeasure [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : MeasureTheory.Measure Bool :=
  ProbCompRuntime.probComp.evalDist
    (gameFourObservation hash enc K <$> gameFour hash enc K adv)

/-- Game 4's unconditioned returned winning mass. -/
noncomputable def gameFourAdvantage [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  gameFourOutputMeasure hash enc K adv {true}

/-- Only a successful forged-epoch record can be removed by the designated-cut check. -/
def successfulSecondChainDifference [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  gameThreeObservation hash enc K out && !gameFourObservation hash enc K out &&
    match forgedEpochSource out with
    | .successful _ _ => true
    | _ => false

/-- Native returned mass removed by the second-chain check. -/
noncomputable def successfulSecondChainDifferenceMass [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist
    (successfulSecondChainDifference hash enc K <$> sourceProgram hash enc K adv) {true}

/-- An unused epoch has identical Game 3 and Game 4 observations. -/
theorem gameFourObservation_unused [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (hsource : forgedEpochSource out = .unused) :
    gameFourObservation hash enc K out = gameThreeObservation hash enc K out := by
  simp [gameFourObservation, designatedCutHolds, hsource]

/-- A failed consumed epoch has identical Game 3 and Game 4 observations. -/
theorem gameFourObservation_failedConsumed [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (msg : M)
    (hsource : forgedEpochSource out = .failedConsumed msg) :
    gameFourObservation hash enc K out = gameThreeObservation hash enc K out := by
  simp [gameFourObservation, designatedCutHolds, hsource]

/-- Every returned Game 3 win is retained by Game 4 or is a successful-record difference. -/
theorem gameThreeObservation_eq_gameFour_or_successfulSecondChainDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) :
    gameThreeObservation hash enc K out =
      (gameFourObservation hash enc K out ||
        successfulSecondChainDifference hash enc K out) := by
  cases hs : forgedEpochSource out with
  | unused => simp [gameFourObservation, designatedCutHolds,
      successfulSecondChainDifference, hs]
  | failedConsumed msg => simp [gameFourObservation, designatedCutHolds,
      successfulSecondChainDifference, hs]
  | successful msg sig =>
    simp only [gameFourObservation, successfulSecondChainDifference, hs]
    cases gameThreeObservation hash enc K out <;>
      cases designatedCutHolds hash enc out <;> decide

/-- The native Game 3 win is bounded by Game 4 plus its successful-record difference. -/
theorem gameThreeAdvantage_le_gameFour_add_successfulSecondChainDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    gameThreeAdvantage hash enc K adv ≤
      gameFourAdvantage hash enc K adv +
        successfulSecondChainDifferenceMass hash enc K adv := by
  simp only [gameThreeAdvantage, gameThreeOutputMeasure, gameThree,
    gameFourAdvantage, gameFourOutputMeasure, gameFour,
    successfulSecondChainDifferenceMass, ProbCompRuntime.probComp_evalDist,
    map_eq_bind_pure_comp]
  apply OracleComp.evalDist_bind_apply_le_add_of_support
    (sourceProgram hash enc K adv)
    (fun out => pure (gameThreeObservation hash enc K out))
    (fun out => pure (gameFourObservation hash enc K out))
    (fun out => pure (successfulSecondChainDifference hash enc K out))
    (by measurability)
  intro out _
  rw [gameThreeObservation_eq_gameFour_or_successfulSecondChainDifference hash enc K out]
  cases gameFourObservation hash enc K out <;>
    cases successfulSecondChainDifference hash enc K out <;> simp

/-- The Game 4 win carried by a successful forged-epoch record. -/
def successfulGameFourObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  gameFourObservation hash enc K out &&
    match forgedEpochSource out with
    | .successful _ _ => true
    | _ => false

/-- The Game 4 win carried by a forged epoch never queried by the signer. -/
def unusedGameFourObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  gameFourObservation hash enc K out &&
    match forgedEpochSource out with
    | .unused => true
    | _ => false

/-- The Game 4 win carried by a failed but consumed forged epoch. -/
def failedConsumedGameFourObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  gameFourObservation hash enc K out &&
    match forgedEpochSource out with
    | .failedConsumed _ => true
    | _ => false

/-- The two distinct non-success forged-epoch observations carried into Game 4. -/
def nonSuccessGameFourObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) : Bool :=
  unusedGameFourObservation hash enc K out ||
    failedConsumedGameFourObservation hash enc K out

/-- The returned Game 4 win is exactly classified by its forged-epoch history. -/
theorem gameFourObservation_eq_successful_or_nonSuccess
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) :
    gameFourObservation hash enc K out =
      (successfulGameFourObservation hash enc K out ||
        nonSuccessGameFourObservation hash enc K out) := by
  cases hs : forgedEpochSource out <;>
    simp [successfulGameFourObservation, nonSuccessGameFourObservation,
      unusedGameFourObservation, failedConsumedGameFourObservation, hs]

/-- Native returned winning mass for successful Game 4 records. -/
noncomputable def successfulGameFourMass [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist
    (successfulGameFourObservation hash enc K <$> sourceProgram hash enc K adv) {true}

/-- Native returned winning mass at unused forged epochs. -/
noncomputable def unusedGameFourMass [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist
    (unusedGameFourObservation hash enc K <$> sourceProgram hash enc K adv) {true}

/-- Native returned winning mass at failed consumed forged epochs. -/
noncomputable def failedConsumedGameFourMass [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist
    (failedConsumedGameFourObservation hash enc K <$> sourceProgram hash enc K adv) {true}

/-- Native returned mass lost when Game 5 rejects non-success histories. -/
noncomputable def nonSuccessGameFourMass [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist
    (nonSuccessGameFourObservation hash enc K <$> sourceProgram hash enc K adv) {true}

/-- A native-measure upper partition of Game 4's returned wins. The non-success summand is
not asserted to vanish or to be bounded by a hardness game. -/
theorem gameFourAdvantage_le_successful_add_nonSuccess
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    gameFourAdvantage hash enc K adv ≤
      successfulGameFourMass hash enc K adv + nonSuccessGameFourMass hash enc K adv := by
  simp only [gameFourAdvantage, gameFourOutputMeasure, gameFour,
    successfulGameFourMass, nonSuccessGameFourMass,
    ProbCompRuntime.probComp_evalDist, map_eq_bind_pure_comp]
  apply OracleComp.evalDist_bind_apply_le_add_of_support
    (sourceProgram hash enc K adv)
    (fun out => pure (gameFourObservation hash enc K out))
    (fun out => pure (successfulGameFourObservation hash enc K out))
    (fun out => pure (nonSuccessGameFourObservation hash enc K out))
    (by measurability)
  intro out _
  rw [gameFourObservation_eq_successful_or_nonSuccess hash enc K out]
  cases successfulGameFourObservation hash enc K out <;>
    cases nonSuccessGameFourObservation hash enc K out <;> simp

/-- The two non-success returned events are kept distinct in the native measure. -/
theorem nonSuccessGameFourMass_le_unused_add_failedConsumed
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    nonSuccessGameFourMass hash enc K adv ≤
      unusedGameFourMass hash enc K adv + failedConsumedGameFourMass hash enc K adv := by
  simp only [nonSuccessGameFourMass, unusedGameFourMass, failedConsumedGameFourMass,
    ProbCompRuntime.probComp_evalDist, map_eq_bind_pure_comp]
  apply OracleComp.evalDist_bind_apply_le_add_of_support
    (sourceProgram hash enc K adv)
    (fun out => pure (nonSuccessGameFourObservation hash enc K out))
    (fun out => pure (unusedGameFourObservation hash enc K out))
    (fun out => pure (failedConsumedGameFourObservation hash enc K out))
    (by measurability)
  intro out _
  simp only [nonSuccessGameFourObservation]
  cases unusedGameFourObservation hash enc K out <;>
    cases failedConsumedGameFourObservation hash enc K out <;> simp

end GXMSS.Reductions
