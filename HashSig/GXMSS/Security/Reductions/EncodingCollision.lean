/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
public import HashSig.GXMSS.Security.Reductions.Problems
import all HashSig.GXMSS.Security.Reductions.Problems
public import HashSig.GXMSS.Security.Reductions.TargetCollision
import all HashSig.GXMSS.Security.Reductions.TargetCollision
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Encoding collision reduction

The source signing interaction is coupled to the bounded encoding transcript, preserving
failed and repeated requests and the actual target-collision experiment.
-/

public section
namespace GXMSS.Reductions
open Encoding ENNReal OracleComp OracleSpec GXMSS.Security TweakableHash
variable {PP T X H M R E S : Type} {h w v n radix : ℕ}
private def encodingSigningOracle
    (hash : HashInstance PP T X H h w v)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch h) M (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v))
        (OracleComp (unifSpec + Encoding.TargetCollisionResistance.challengeSpec
          M R (Epoch h) v (2 ^ w)))) := fun q history =>
  match history q.1 with
  | some _ => pure (none, history)
  | none => do
      let answer ← liftM ((unifSpec + Encoding.TargetCollisionResistance.challengeSpec
        M R (Epoch h) v (2 ^ w)).query (.inr (q.2, q.1)))
      let signature := answer.map (GXMSS.signatureOfWord hash sk q.1)
      return (signature, Function.update history q.1 (some (q.2, signature)))
private theorem encodingSigningOracle_used
    (hash : HashInstance PP T X H h w v)
    (sk : GXMSS.SecretKey PP H h v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg first : M) (answer : Option (GXMSS.Signature R H h v))
    (hused : history ep = some (first, answer)) :
    (encodingSigningOracle hash sk (ep, msg)).run history = pure (none, history) := by
  change encodingSigningOracle hash sk (ep, msg) history = _
  simp [encodingSigningOracle, hused]
private theorem encodingSigningOracle_unused
    (hash : HashInstance PP T X H h w v)
    (sk : GXMSS.SecretKey PP H h v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg : M) (hunused : history ep = none) :
    (encodingSigningOracle hash sk (ep, msg)).run history = (do
      let answer ← ((unifSpec + TargetCollisionResistance.challengeSpec M R
        (Epoch h) v (2 ^ w)).query (.inr (msg, ep)))
      let signature := answer.map (GXMSS.signatureOfWord hash sk ep)
      pure (signature, Function.update history ep (some (msg, signature)))) := by
  change encodingSigningOracle hash sk (ep, msg) history = _
  simp [encodingSigningOracle, hunused]
/-- A source signing handler that retains the successful or exhausted encoding record alongside
the exact signing history.  Its first projection is the ordinary source signing handler. -/
private def encodingSourceCoupledImpl [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) ProbComp) :=
  fun q state =>
    match q with
    | .inl uniform => do
        let answer ← liftM ((unifSpec.query uniform) : ProbComp _)
        return (answer, state)
    | .inr (ep, msg) =>
        match state.1 ep with
        | some _ => pure (none, state)
        | none => do
            let answer ← enc.retry ($ᵗ R) sk.seed msg ep K
            let signature := answer.map (GXMSS.signatureOfWord hash sk ep)
            let history := Function.update state.1 ep (some (msg, signature))
            let transcript := state.2 ++ [⟨ep, msg, answer⟩]
            return (signature, (history, transcript))
private def sourceSigningImpl [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) ProbComp) +
    SyncSignatureUnforgeability.signingOracle (GXMSS.scheme hash enc K) sk
/-- The coupled source handler projects to the exact admitted synchronized-signature
handler, including returned failure. -/
private theorem encodingSourceCoupledImpl_proj [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) :
    Prod.map id Prod.fst <$> (encodingSourceCoupledImpl hash enc K sk q).run state =
      (sourceSigningImpl hash enc K sk q).run state.1 := by
  cases q with
  | inl uniform =>
    change Prod.map id Prod.fst <$> encodingSourceCoupledImpl hash enc K sk (.inl uniform)
      state = sourceSigningImpl hash enc K sk (.inl uniform) state.1
    dsimp [encodingSourceCoupledImpl, sourceSigningImpl]
    simp [map_eq_bind_pure_comp, bind_assoc]
    rfl
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change Prod.map id Prod.fst <$> encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg))
      state = sourceSigningImpl hash enc K sk (.inr (ep, msg)) state.1
    by_cases hused : state.1 ep = none
    · dsimp [encodingSourceCoupledImpl, sourceSigningImpl,
        SyncSignatureUnforgeability.signingOracle]
      rw [hused]
      simp [GXMSS.scheme, GXMSS.sign, map_eq_bind_pure_comp, bind_assoc, hused]
    · cases hentry : state.1 ep with
      | none => exact False.elim (hused hentry)
      | some entry =>
        dsimp [encodingSourceCoupledImpl, sourceSigningImpl,
          SyncSignatureUnforgeability.signingOracle]
        rw [hentry]
        simp
/-- First-request consumption agrees between the synchronized signing history and the
encoding target transcript. -/
private def encodingHistoryMatches
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (transcript : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) : Prop :=
  ∀ ep, (history ep = none ↔ TargetCollisionResistance.used transcript ep = false)
private theorem encodingHistoryMatches_empty :
    encodingHistoryMatches (H := H) (M := M) (R := R) (h := h) (v := v) (w := w)
      (SyncSignatureUnforgeability.emptyHistory (E := Epoch h) (M := M)
        (S := GXMSS.Signature R H h v))
      ([] : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) := by
  intro ep
  simp [SyncSignatureUnforgeability.emptyHistory, TargetCollisionResistance.used]
private theorem encodingSourceCoupledImpl_preserves_match [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hmatch : encodingHistoryMatches state.1 state.2)
    (out : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Range q ×
      (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support ((encodingSourceCoupledImpl hash enc K sk q).run state)) :
    encodingHistoryMatches out.2.1 out.2.2 := by
  cases q with
  | inl uniform =>
    change out ∈ support
      ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at hout
    simp only [mem_support_bind_iff] at hout
    obtain ⟨answer, _, hreturn⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hreturn
    subst out
    exact hmatch
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change out ∈ support (encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg))
      state) at hout
    dsimp [encodingSourceCoupledImpl] at hout
    by_cases hused : state.1 ep = none
    · rw [hused] at hout
      change out ∈ support
        ((enc.retry ($ᵗ R) sk.seed msg ep K) >>= fun answer =>
          pure (answer.map (GXMSS.signatureOfWord hash sk ep),
            (Function.update state.1 ep
              (some (msg, answer.map (GXMSS.signatureOfWord hash sk ep))),
              state.2 ++ [⟨ep, msg, answer⟩]))) at hout
      obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
      have hreturn' := (mem_support_pure_iff _ _).mp hreturn
      subst out
      intro other
      by_cases heq : other = ep
      · subst other
        simp [Function.update, TargetCollisionResistance.used]
      · have hprev := hmatch other
        have hne : ep ≠ other := Ne.symm heq
        simpa [Function.update, heq, hne, TargetCollisionResistance.used,
          List.any_append] using hprev
    · cases hentry : state.1 ep with
      | none => exact False.elim (hused hentry)
      | some entry =>
        rw [hentry] at hout
        simp only [support_pure, Set.mem_singleton_iff] at hout
        subst out
        exact hmatch
/-- Forgetting only the auxiliary encoding transcript recovers the actual source interaction. -/
private theorem encodingSourceCoupled_run_proj [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pk : GXMSS.PublicKey PP H) :
    Prod.map id Prod.fst <$>
      (simulateQ (encodingSourceCoupledImpl hash enc K sk) (adv.forge pk)).run
        (SyncSignatureUnforgeability.emptyHistory, []) =
      (simulateQ (sourceSigningImpl hash enc K sk) (adv.forge pk)).run
        SyncSignatureUnforgeability.emptyHistory := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (encodingSourceCoupledImpl hash enc K sk) (sourceSigningImpl hash enc K sk)
    Prod.fst (fun q state => encodingSourceCoupledImpl_proj hash enc K sk q state)
    (adv.forge pk) (SyncSignatureUnforgeability.emptyHistory, [])
private def encodingGameInnerImpl
    (hash : HashInstance PP T X H h w v)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))
        (OracleComp (unifSpec + TargetCollisionResistance.challengeSpec
          M R (Epoch h) v (2 ^ w)))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (unifSpec +
    TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) (OracleComp (unifSpec +
          TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))) +
    encodingSigningOracle (M := M) (R := R) (h := h) (w := w) (v := v) hash sk
/-- The fixed reduction's signing handler interpreted by the authoritative encoding challenge
oracle, with both state components retained. -/
private def encodingGameCoupledImpl [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) :
    QueryImpl (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) ProbComp) :=
  ((TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) sk.seed).mapStateTBase
    (encodingGameInnerImpl (M := M) (R := R) hash sk)).flattenStateT
private theorem encodingGameCoupledImpl_eq_source_of_capacity [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hmatch : encodingHistoryMatches state.1 state.2)
    (hspace : q.isRight = true → state.2.length < qs) :
    (encodingGameCoupledImpl hash enc qs K sk q).run state =
      (encodingSourceCoupledImpl hash enc K sk q).run state := by
  cases q with
  | inl uniform =>
    change encodingGameCoupledImpl hash enc qs K sk (.inl uniform) state =
      encodingSourceCoupledImpl hash enc K sk (.inl uniform) state
    simp [encodingGameCoupledImpl, encodingGameInnerImpl,
      encodingSourceCoupledImpl, TargetCollisionResistance.oracles,
      QueryImpl.flattenStateT, QueryImpl.mapStateTBase]
    dsimp [StateT.mk]
    rfl
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change encodingGameCoupledImpl hash enc qs K sk (.inr (ep, msg)) state =
      encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg)) state
    by_cases hused : state.1 ep = none
    · have hfresh : TargetCollisionResistance.used state.2 ep = false :=
        (hmatch ep).mp hused
      have hlen : state.2.length < qs := hspace (by simp)
      have hcap := encodingFreshQuery_capacity qs state.2 ep hlen hfresh
      simp only [add_apply_inr, InductiveMerkleTree.range_def,
        encodingGameCoupledImpl, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, TargetCollisionResistance.oracles,
        QueryImpl.ofLift_eq_id', encodingTCRProblem, encodingGameInnerImpl,
        QueryImpl.add_apply_inr, StateT.run_mk, map_eq_bind_pure_comp,
        encodingSourceCoupledImpl, hused, bind_pure_comp]
      dsimp [StateT.mk]
      rw [encodingSigningOracle_unused hash sk state.1 ep msg hused]
      simp [simulateQ_bind, simulateQ_query,
        TargetCollisionResistance.challengeOracle, hcap,
        TargetCollisionResistance.finish, TargetCollisionResistance.retry,
        map_eq_bind_pure_comp, bind_assoc]
    · cases hentry : state.1 ep with
      | none => exact False.elim (hused hentry)
      | some entry =>
        simp only [add_apply_inr, InductiveMerkleTree.range_def,
          encodingGameCoupledImpl, QueryImpl.flattenStateT,
          QueryImpl.mapStateTBase, TargetCollisionResistance.oracles,
          QueryImpl.ofLift_eq_id', encodingGameInnerImpl,
          QueryImpl.add_apply_inr, StateT.run_mk,
          encodingSourceCoupledImpl, hentry]
        dsimp [StateT.mk]
        rw [encodingSigningOracle_used hash sk state.1 ep msg entry.1 entry.2 hentry]
        simp
private theorem encodingSourceCoupledImpl_length [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (out : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Range q ×
      (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support ((encodingSourceCoupledImpl hash enc K sk q).run state)) :
    out.2.2.length ≤ state.2.length + (if q matches .inr _ then 1 else 0) := by
  cases q with
  | inl uniform =>
    change out ∈ support
      ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at hout
    obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
    have heq := (mem_support_pure_iff _ _).mp hreturn
    subst out
    simp
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change out ∈ support (encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg))
      state) at hout
    dsimp [encodingSourceCoupledImpl] at hout
    cases hentry : state.1 ep with
    | some entry =>
      rw [hentry] at hout
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      simp
    | none =>
      rw [hentry] at hout
      obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
      have heq := (mem_support_pure_iff _ _).mp hreturn
      subst out
      simp
/-- Every successful signing reply in the coupled state names an admitted, successful
encoding challenge record and its exact word/randomizer. -/
private def encodingSuccessfulRecordsMatch
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) : Prop :=
  ∀ ep msg sig, state.1 ep = some (msg, some sig) →
    ∃ wr, (⟨ep, msg, some wr⟩ : TargetCollisionResistance.Record M R
      (Epoch h) v (2 ^ w)) ∈ state.2 ∧
      sig = GXMSS.signatureOfWord hash sk ep wr ∧
      enc.value sk.seed msg wr.2 ep = some wr.1
private theorem encodingSuccessfulRecordsMatch_empty
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) :
    encodingSuccessfulRecordsMatch hash enc sk
      (SyncSignatureUnforgeability.emptyHistory, []) := by
  intro ep msg sig hrecord
  simp [SyncSignatureUnforgeability.emptyHistory] at hrecord
private theorem encodingSourceCoupledImpl_preserves_successfulRecords [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (q : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Domain)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hinv : encodingSuccessfulRecordsMatch hash enc sk state)
    (out : (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v)).Range q ×
      (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support ((encodingSourceCoupledImpl hash enc K sk q).run state)) :
    encodingSuccessfulRecordsMatch hash enc sk out.2 := by
  cases q with
  | inl uniform =>
    change out ∈ support
      ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at hout
    obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
    have heq := (mem_support_pure_iff _ _).mp hreturn
    subst out
    exact hinv
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change out ∈ support (encodingSourceCoupledImpl hash enc K sk (.inr (ep, msg))
      state) at hout
    dsimp [encodingSourceCoupledImpl] at hout
    cases hentry : state.1 ep with
    | some entry =>
      rw [hentry] at hout
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      exact hinv
    | none =>
      rw [hentry] at hout
      obtain ⟨answer, hanswer, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
      have heq := (mem_support_pure_iff _ _).mp hreturn
      subst out
      intro other first signature hrecord
      by_cases heq : other = ep
      · subst other
        cases answer with
        | none => simp [Function.update] at hrecord
        | some wr =>
          have hpair : first = msg ∧ signature = GXMSS.signatureOfWord hash sk ep wr := by
            simpa [Function.update] using hrecord.symm
          rcases hpair with ⟨hfirst, hsignature⟩
          refine ⟨wr, ?_, hsignature, ?_⟩
          · simp [hfirst]
          · simpa [hfirst] using IncomparableEncoding.Retry.value_eq_some_of_mem_retry
              enc ($ᵗ R) sk.seed msg ep K wr.1 wr.2 hanswer
      · have hold : state.1 other = some (first, some signature) := by
          simpa [Function.update, heq] using hrecord
        obtain ⟨wr, hmem, hsig, hword⟩ := hinv other first signature hold
        exact ⟨wr, List.mem_append.mpr (Or.inl hmem), hsig, hword⟩
/-- On a returned successful-record difference, the coupled transcript makes the exact
fixed encoding reduction candidate win the authoritative target-collision predicate. -/
private theorem encodingSuccessfulDifference_valid [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v) (out : Result PP H M R h v)
    (transcript : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hseed : out.pk.seed = sk.seed)
    (hrecords : encodingSuccessfulRecordsMatch hash enc sk (out.history, transcript))
    (hdiff : successfulEncodingDifference hash enc K out = true) :
    TargetCollisionResistance.valid enc sk.seed transcript
      (out.forgery.2.1, out.forgery.2.2.randomizer, out.forgery.1) = true := by
  cases hsource : forgedEpochSource out with
  | unused => simp [successfulEncodingDifference, hsource] at hdiff
  | failedConsumed msg => simp [successfulEncodingDifference, hsource] at hdiff
  | successful msg sig =>
    have hd : gameOneObservation hash enc K out = true ∧
        (!gameTwoObservation hash enc K out) = true := by
      simpa only [successfulEncodingDifference, hsource, Bool.and_true,
        Bool.and_eq_true] using hdiff
    have hwin : gameOneObservation hash enc K out = true := by
      exact hd.1
    have hremoved : gameTwoObservation hash enc K out = false := by
      cases htwo : gameTwoObservation hash enc K out <;> simp [htwo] at hd ⊢
    have hrecord := history_of_successful_source out msg sig hsource
    obtain ⟨wr, hmem, hsig, hvalue⟩ := hrecords out.forgery.1 msg sig hrecord
    have hhonest : ∃ word, enc.value out.pk.seed msg sig.randomizer
        out.forgery.1 = some word := by
      refine ⟨wr.1, ?_⟩
      simpa [hseed, hsig, GXMSS.signatureOfWord] using hvalue
    obtain ⟨word, hhonestWord, hforgedWord, hne⟩ :=
      successful_encoding_difference_witness hash enc K out msg sig hsource
        hhonest hwin hremoved
    have hword : word = wr.1 := by
      rw [hseed] at hhonestWord
      have hsigR : sig.randomizer = wr.2 := by simp [hsig, GXMSS.signatureOfWord]
      rw [hsigR, hvalue] at hhonestWord
      exact Option.some.inj hhonestWord.symm
    apply encodingTargetValid_of_successful_record enc sk.seed transcript
      out.forgery.1 msg out.forgery.2.1 wr.2 out.forgery.2.2.randomizer wr.1 hmem
    · simpa [hseed, hword] using hforgedWord
    · simpa [hsig, GXMSS.signatureOfWord] using hne
private theorem encodingSourceCoupled_run_successfulRecords
     [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pk : GXMSS.PublicKey PP H)
    (out : (Epoch h × (M × GXMSS.Signature R H h v)) ×
      (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support
      ((simulateQ (encodingSourceCoupledImpl hash enc K sk) (adv.forge pk)).run
        (SyncSignatureUnforgeability.emptyHistory, []))) :
    encodingSuccessfulRecordsMatch hash enc sk out.2 := by
  classical
  apply OracleComp.simulateQ_run_preservesInv
    (encodingSourceCoupledImpl hash enc K sk)
    (encodingSuccessfulRecordsMatch hash enc sk)
    (fun q state hstate answer hans =>
      encodingSourceCoupledImpl_preserves_successfulRecords hash enc K sk q state
        hstate answer hans)
    (adv.forge pk) (SyncSignatureUnforgeability.emptyHistory, [])
  · intro ep msg sig hrecord
    simp [SyncSignatureUnforgeability.emptyHistory] at hrecord
  · exact hout
/-- Honest source generation with the challenge transcript retained only for the coupling. -/
private def encodingSourceCoupledProgram [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    ProbComp (Result PP H M R h v ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) := do
  let pp ← (HashInstance.thf hash).seedGen
  let starts ← GXMSS.sampleStarts H h v
  let keys := GXMSS.keys hash pp starts
  let (forgery, state) ←
    (simulateQ (encodingSourceCoupledImpl hash enc K keys.2) (adv.forge keys.1)).run
      (SyncSignatureUnforgeability.emptyHistory, [])
  return (⟨keys.1, keys.2, forgery, state.1⟩, state.2)
private theorem encodingSourceCoupledProgram_proj [SampleableType H] [SampleableType R]
    [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) :
    Prod.fst <$> encodingSourceCoupledProgram hash enc K adv =
      sourceProgram hash enc K adv := by
  simp only [encodingSourceCoupledProgram, sourceProgram, GXMSS.keygen,
    runWithKeys, map_bind, map_pure, bind_assoc]
  congr 1
  funext pp
  congr 1
  funext starts
  let keys := GXMSS.keys hash pp starts
  simp only [pure_bind]
  have hproj := congrArg
    (fun c => (fun z => (⟨keys.1, keys.2, z.1, z.2⟩ : Result PP H M R h v)) <$> c)
    (encodingSourceCoupled_run_proj hash enc K keys.2 adv keys.1)
  simpa only [sourceSigningImpl, Functor.map_map, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq] using hproj
private theorem encodingSourceCoupledProgram_support [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hout : out ∈ support (encodingSourceCoupledProgram hash enc K adv)) :
    out.1.pk.seed = out.1.sk.seed ∧
      encodingSuccessfulRecordsMatch hash enc out.1.sk (out.1.history, out.2) := by
  unfold encodingSourceCoupledProgram at hout
  obtain ⟨pp, _, hrest⟩ := support_bind_exists hout
  obtain ⟨starts, _, hrest⟩ := support_bind_exists hrest
  obtain ⟨runout, hrun, hret⟩ := support_bind_exists hrest
  have heq := (mem_support_pure_iff _ _).mp hret
  subst out
  constructor
  · rfl
  · exact encodingSourceCoupled_run_successfulRecords hash enc K
      (GXMSS.keys hash pp starts).2 adv (GXMSS.keys hash pp starts).1 runout hrun
/-- A pathwise source signing bound leaves strict transcript room before each permitted
signing call, so the actual challenge handler fits the `qs`-record problem. -/
private theorem encodingGameCoupled_run_eq_source_of_bound {α : Type} [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (sk : GXMSS.SecretKey PP H h v)
    (oa : OracleComp (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Epoch h) M (GXMSS.Signature R H h v)) α)
    (budget : ℕ)
    (hbound : oa.IsQueryBoundP (fun q => q.isRight = true) budget)
    (state : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hmatch : encodingHistoryMatches state.1 state.2)
    (hlen : state.2.length + budget ≤ qs) :
    (simulateQ (encodingGameCoupledImpl hash enc qs K sk) oa).run state =
      (simulateQ (encodingSourceCoupledImpl hash enc K sk) oa).run state := by
  induction oa using OracleComp.inductionOn generalizing budget state with
  | pure value => rfl
  | query_bind q next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind]
    have hspace : q.isRight = true → state.2.length < qs := by
      intro hsign
      cases q with
      | inl uniform => simp at hsign
      | inr signing =>
        have hpositive : 0 < budget := hbound.1.resolve_left (by simp)
        omega
    rw [encodingGameCoupledImpl_eq_source_of_capacity hash enc qs K sk q state
      hmatch hspace]
    apply bind_congr_of_forall_mem_support
    intro output houtput
    have hmatch' := encodingSourceCoupledImpl_preserves_match hash enc K sk q
      state hmatch output houtput
    have hstep := encodingSourceCoupledImpl_length hash enc K sk q state output houtput
    have hnext : output.2.2.length +
        (if q.isRight = true then budget - 1 else budget) ≤ qs := by
      cases q with
      | inl uniform =>
        simp only [Sum.isRight, Bool.false_eq_true, ite_false] at hstep ⊢
        omega
      | inr signing =>
        simp only [Sum.isRight, ite_true] at hstep ⊢
        have hpositive : 0 < budget := hbound.1.resolve_left (by simp)
        omega
    exact ih output.1 (if q.isRight = true then budget - 1 else budget)
      (hbound.2 output.1) output.2 hmatch' hnext
/-- Encoding target-collision reduction using only the successful source transcript. -/
noncomputable def encodingTargetCollisionReduction [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (advGXMSS : SchemeAdversary PP H M R h v) :
    Encoding.TargetCollisionResistance.Adversary (encodingTCRProblem hash enc qs K) where
  find pp := do
    let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
    let keys := GXMSS.keys hash pp starts
    let impl : QueryImpl
        (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
          (GXMSS.Signature R H h v))
        (StateT (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v)) (OracleComp (unifSpec +
            Encoding.TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))) :=
      (QueryImpl.ofLift unifSpec (OracleComp (unifSpec +
        Encoding.TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))).liftTarget
          (StateT (SyncSignatureUnforgeability.History (Epoch h) M
            (GXMSS.Signature R H h v)) (OracleComp (unifSpec +
              Encoding.TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))) +
        encodingSigningOracle (M := M) (R := R) (h := h) (w := w) (v := v) hash keys.2
    let (forgery, _history) ←
      (simulateQ impl (advGXMSS.forge keys.1)).run SyncSignatureUnforgeability.emptyHistory
    let forgedEpoch := forgery.1
    let forgedPayload := forgery.2
    let forgedMessage := forgedPayload.1
    let forgedSignature := forgedPayload.2
    return (forgedMessage, forgedSignature.randomizer, forgedEpoch)
private def encodingFinalFind
    (out : Result PP H M R h v) :
    OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R
      (Epoch h) v (2 ^ w)) (M × R × Epoch h) :=
  pure (out.forgery.2.1, out.forgery.2.2.randomizer, out.forgery.1)
private noncomputable def encodingTargetTail [SampleableType R]
    [DecidableEq M] [DecidableEq R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (out : Result PP H M R h v ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) : ProbComp Bool := do
  let (collision, transcript) ←
    (simulateQ
      (TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) out.1.sk.seed)
      (encodingFinalFind out.1)).run out.2
  return TargetCollisionResistance.valid enc out.1.sk.seed transcript collision
private theorem encodingTargetTail_successfulDifference
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (out : Result PP H M R h v ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hseed : out.1.pk.seed = out.1.sk.seed)
    (hrecords : encodingSuccessfulRecordsMatch hash enc out.1.sk
      (out.1.history, out.2))
    (hdiff : successfulEncodingDifference hash enc K out.1 = true) :
    encodingTargetTail hash enc qs K out = pure true := by
  have hvalid := encodingSuccessfulDifference_valid hash enc K out.1.sk
    out.1 out.2 hseed hrecords hdiff
  cases hsource : forgedEpochSource out.1 with
  | unused => simp [successfulEncodingDifference, hsource] at hdiff
  | failedConsumed msg => simp [successfulEncodingDifference, hsource] at hdiff
  | successful msg sig =>
    simp [encodingTargetTail, encodingFinalFind, hvalid, simulateQ_pure]
private theorem encodingOuter_liftStarts [SampleableType H] [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (pp : PP) :
    (simulateQ (TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) pp)
      (OracleComp.liftComp (GXMSS.sampleStarts H h v)
        (unifSpec + TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))).run
      ([] : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) =
    (fun starts => (starts, ([] : TargetCollisionResistance.Transcript M R
      (Epoch h) v (2 ^ w)))) <$> GXMSS.sampleStarts H h v := by
  simp [TargetCollisionResistance.oracles, QueryImpl.simulateQ_add_liftM_left,
    simulateQ_liftTarget]
private theorem encodingOuter_inner_run_eq_source [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs)
    (pp : PP) (starts : Epoch h → Fin v → H) :
    let keys := GXMSS.keys hash pp starts
    (simulateQ
      ((TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) pp).mapStateTBase
        (encodingGameInnerImpl (M := M) (R := R) hash keys.2)).flattenStateT
      (adv.forge keys.1)).run (SyncSignatureUnforgeability.emptyHistory, []) =
    (simulateQ (encodingSourceCoupledImpl hash enc K keys.2)
      (adv.forge keys.1)).run (SyncSignatureUnforgeability.emptyHistory, []) := by
  dsimp
  change (simulateQ (encodingGameCoupledImpl hash enc qs K (GXMSS.keys hash pp starts).2)
    (adv.forge (GXMSS.keys hash pp starts).1)).run
      (SyncSignatureUnforgeability.emptyHistory, []) = _
  exact encodingGameCoupled_run_eq_source_of_bound hash enc qs K
    (GXMSS.keys hash pp starts).2 (adv.forge (GXMSS.keys hash pp starts).1) qs
    (hbound (GXMSS.keys hash pp starts).1)
    (SyncSignatureUnforgeability.emptyHistory, [])
    encodingHistoryMatches_empty (by simp)
private theorem encodingNested_run_eq_source [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs)
    (pp : PP) (starts : Epoch h → Fin v → H) :
    let keys := GXMSS.keys hash pp starts
    (simulateQ (TargetCollisionResistance.oracles (encodingTCRProblem hash enc qs K) pp)
      ((simulateQ
        ((QueryImpl.ofLift unifSpec (OracleComp (unifSpec +
          TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))).liftTarget
            (StateT (SyncSignatureUnforgeability.History (Epoch h) M
              (GXMSS.Signature R H h v)) (OracleComp (unifSpec +
                TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))) +
          encodingSigningOracle (M := M) (R := R) (h := h) (w := w) (v := v) hash keys.2)
        (adv.forge keys.1)).run SyncSignatureUnforgeability.emptyHistory)).run
      ([] : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) =
    (fun z => ((z.1, z.2.1), z.2.2)) <$>
      (simulateQ (encodingSourceCoupledImpl hash enc K keys.2)
        (adv.forge keys.1)).run (SyncSignatureUnforgeability.emptyHistory, []) := by
  dsimp
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun z => ((z.1, z.2.1), z.2.2)) <$>
      (simulateQ (encodingGameCoupledImpl hash enc qs K (GXMSS.keys hash pp starts).2)
        (adv.forge (GXMSS.keys hash pp starts).1)).run
        (SyncSignatureUnforgeability.emptyHistory, []) = _
  exact congrArg (fun c => (fun z => ((z.1, z.2.1), z.2.2)) <$> c)
    (encodingGameCoupled_run_eq_source_of_bound hash enc qs K
      (GXMSS.keys hash pp starts).2 (adv.forge (GXMSS.keys hash pp starts).1) qs
      (hbound (GXMSS.keys hash pp starts).1)
      (SyncSignatureUnforgeability.emptyHistory, [])
      encodingHistoryMatches_empty (by simp))
private theorem encodingTargetExperiment_eq_coupled
    [SampleableType H] [SampleableType R]
     [DecidableEq M] [DecidableEq R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    TargetCollisionResistance.experiment
      (encodingTargetCollisionReduction hash enc qs K adv) =
      encodingSourceCoupledProgram hash enc K adv >>= encodingTargetTail hash enc qs K := by
  unfold TargetCollisionResistance.experiment encodingTargetCollisionReduction
  unfold encodingSourceCoupledProgram encodingTargetTail
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]
  simp only [encodingOuter_liftStarts]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  apply congrArg (fun (f : PP → ProbComp Bool) => hash.thf.seedGen >>= f)
  funext pp
  apply congrArg (fun (f : (Epoch h → Fin v → H) → ProbComp Bool) =>
    GXMSS.sampleStarts H h v >>= f)
  funext starts
  rw [encodingNested_run_eq_source hash enc qs K adv hbound pp starts]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl
/-- Native winning mass of the successful-record Game 1 to Game 2 difference is bounded by
the exact authoritative target-collision experiment. The unused and failed-consumed cases
contribute no mass to this event; any unreturned mass remains unconditioned. -/
theorem successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    successfulEncodingDifferenceMass hash enc K adv ≤
      TargetCollisionResistance.advantage
        (encodingTargetCollisionReduction hash enc qs K adv) := by
  have hprogram :
      (successfulEncodingDifference hash enc K <$> sourceProgram hash enc K adv) =
        (fun z => successfulEncodingDifference hash enc K z.1) <$>
          encodingSourceCoupledProgram hash enc K adv := by
    rw [← encodingSourceCoupledProgram_proj hash enc K adv]
    simp only [Functor.map_map]
  unfold successfulEncodingDifferenceMass TargetCollisionResistance.advantage
    TargetCollisionResistance.outputMeasure
  rw [hprogram, encodingTargetExperiment_eq_coupled hash enc qs K adv hbound]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (encodingSourceCoupledProgram hash enc K adv)
    (fun z => pure (successfulEncodingDifference hash enc K z.1))
    (encodingTargetTail hash enc qs K) (measurableSet_singleton true)
  intro out hout
  by_cases hdiff : successfulEncodingDifference hash enc K out.1 = true
  · obtain ⟨hseed, hrecords⟩ :=
      encodingSourceCoupledProgram_support hash enc K adv out hout
    rw [encodingTargetTail_successfulDifference hash enc qs K out hseed hrecords hdiff]
    simp [hdiff]
  · have hfalse : successfulEncodingDifference hash enc K out.1 = false := by
      cases h : successfulEncodingDifference hash enc K out.1 <;> simp_all
    simp [hfalse]

end GXMSS.Reductions
