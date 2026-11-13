/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.Adversary
public import HashSig.GXMSS.Security.Interval.Auxiliary.Interaction
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionResistance
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.EvalDist.Sum

/-!
# Native interval encoding target collision simulation

The named encoding adversary uses the actual source seed and retries. Its finite transcript
capacity is bounded by every issued signing request, including failures and repeated epochs.
-/

public section
namespace GXMSS.Reductions
open IncomparableEncoding OracleComp OracleSpec
variable {PP T X H M R : Type} {h w v : ℕ}

/-- Encoding target-collision problem with the all-request record and retry budgets. -/
@[expose] def encodingTCRProblem [SampleableType R] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) :=
  IncomparableEncoding.TargetCollisionResistance.Problem.mk enc
    (HashInstance.thf hash).seedGen ($ᵗ R) qs K

end GXMSS.Reductions

namespace GXMSS.Interval.Reductions
open IncomparableEncoding ENNReal OracleComp OracleSpec SyncSignatureUnforgeability
    GXMSS.Reductions GXMSS.IntervalMerkle
variable {PP T X H M R : Type} {h w v : ℕ}

private def intervalEncodingSign
    (P : HashInstance PP T X H h w v) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) (ep : Epoch h) (msg : M) :
    OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w))
      (Option (GXMSS.Signature R H h v)) :=
  if Epoch.IsActive I ep then
    Option.map (GXMSS.Interval.signatureOfWord P I sk ep) <$>
      (unifSpec + TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)).query
        (.inr (msg, ep))
  else pure none

private def intervalEncodingSigningOracle
    (P : HashInstance PP T X H h w v) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) :=
  signingKernelOracle (intervalEncodingSign (M := M) (R := R) P I sk)

private theorem intervalEncodingSigningOracle_used
    (P : HashInstance PP T X H h w v) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (history : History (Epoch h) M (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg first : M) (answer : Option (GXMSS.Signature R H h v))
    (hused : history ep = some (first, answer)) :
    (intervalEncodingSigningOracle P I sk (ep, msg)).run history = pure (none, history) := by
  change intervalEncodingSigningOracle P I sk (ep, msg) history = _
  exact signingKernelOracle_used _ history ep msg first answer hused

private theorem intervalEncodingSigningOracle_inactive
    (P : HashInstance PP T X H h w v) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (history : History (Epoch h) M (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg : M) (hfresh : history ep = none) (hinactive : ¬ Epoch.IsActive I ep) :
    (intervalEncodingSigningOracle P I sk (ep, msg)).run history =
      pure (none, Function.update history ep (some (msg, none))) := by
  change intervalEncodingSigningOracle P I sk (ep, msg) history = _
  unfold intervalEncodingSigningOracle
  rw [signingKernelOracle_unused _ _ _ _ hfresh]
  simp [intervalEncodingSign, hinactive]
  rfl

private theorem intervalEncodingSigningOracle_active
    (P : HashInstance PP T X H h w v) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (history : History (Epoch h) M (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg : M) (hfresh : history ep = none) (hactive : Epoch.IsActive I ep) :
    (intervalEncodingSigningOracle P I sk (ep, msg)).run history = (do
      let answer ← ((unifSpec + TargetCollisionResistance.challengeSpec
        M R (Epoch h) v (2 ^ w)).query (.inr (msg, ep)))
      let signature := answer.map (GXMSS.Interval.signatureOfWord P I sk ep)
      pure (signature, Function.update history ep (some (msg, signature)))) := by
  change intervalEncodingSigningOracle P I sk (ep, msg) history = _
  unfold intervalEncodingSigningOracle
  rw [signingKernelOracle_unused _ _ _ _ hfresh]
  simp [intervalEncodingSign, hactive, map_eq_bind_pure_comp, bind_assoc]

private def intervalEncodingInnerImpl
    (P : HashInstance PP T X H h w v) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) :
    QueryImpl (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v))
      (StateT (History (Epoch h) M (GXMSS.Signature R H h v))
        (OracleComp (unifSpec + TargetCollisionResistance.challengeSpec
          M R (Epoch h) v (2 ^ w)))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (unifSpec +
    TargetCollisionResistance.challengeSpec M R (Epoch h) v (2 ^ w)))).liftTarget
      (StateT (History (Epoch h) M (GXMSS.Signature R H h v))
        (OracleComp (unifSpec + TargetCollisionResistance.challengeSpec
          M R (Epoch h) v (2 ^ w)))) + intervalEncodingSigningOracle (M := M) (R := R) P I sk

/-- The actual encoding target-collision adversary uses interval paths and makes no encoding
query for an inactive first request. Its total program preserves the original retry budget. -/
noncomputable def encodingTargetCollisionReduction [SampleableType H] [SampleableType R]
     (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v)) :
    TargetCollisionResistance.Adversary (encodingTCRProblem P enc qs K) where
  find pp := do
    let starts ← OracleComp.liftComp (GXMSS.sampleStarts H h v) _
    let fillers ← OracleComp.liftComp (GXMSS.IntervalMerkle.sampleFillers I H) _
    let (pk, sk) := GXMSS.Interval.keys P I pp starts fillers
    let (forgery, _history) ←
      (simulateQ (intervalEncodingInnerImpl P I sk) (A.forge pk)).run emptyHistory
    let (epoch, message, signature) := forgery
    return (message, signature.randomizer, epoch)

private def intervalEncodingSourceImpl [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) :
    QueryImpl (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v))
      (StateT (History (Epoch h) M (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) ProbComp) :=
  let completeKey := sk.complete
  let pp := completeKey.seed
  fun q state =>
    match q with
    | .inl uniform => do
      let answer ← liftM ((unifSpec.query uniform) : ProbComp _)
      return (answer, state)
    | .inr (ep, msg) =>
      match state.1 ep with
      | some _ => pure (none, state)
      | none =>
        if Epoch.IsActive I ep then do
          let answer ← enc.retry ($ᵗ R) pp msg ep K
          let signature := answer.map (GXMSS.Interval.signatureOfWord P I sk ep)
          let history := Function.update state.1 ep (some (msg, signature))
          return (signature, (history, state.2 ++ [⟨ep, msg, answer⟩]))
        else pure (none, (Function.update state.1 ep (some (msg, none)), state.2))

private noncomputable def intervalSourceImpl [SampleableType H] [SampleableType R]
    [DecidableEq H] (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) :
    QueryImpl (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v))
      (StateT (History (Epoch h) M (GXMSS.Signature R H h v)) ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
    (StateT (History (Epoch h) M (GXMSS.Signature R H h v)) ProbComp) +
      signingOracle (GXMSS.Interval.scheme P enc K I) sk

private theorem intervalEncodingSourceImpl_proj [SampleableType H] [SampleableType R]
    [DecidableEq H] (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (q : (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)).Domain)
    (state : History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) :
    Prod.map id Prod.fst <$> (intervalEncodingSourceImpl P enc K I sk q).run state =
      (intervalSourceImpl P enc K I sk q).run state.1 := by
  cases q with
  | inl uniform =>
    change Prod.map id Prod.fst <$> intervalEncodingSourceImpl P enc K I sk (.inl uniform)
      state = intervalSourceImpl P enc K I sk (.inl uniform) state.1
    dsimp [intervalEncodingSourceImpl, intervalSourceImpl]
    simp [map_eq_bind_pure_comp, bind_assoc]
    rfl
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change Prod.map id Prod.fst <$> intervalEncodingSourceImpl P enc K I sk (.inr (ep, msg))
      state = intervalSourceImpl P enc K I sk (.inr (ep, msg)) state.1
    by_cases hused : state.1 ep = none
    · dsimp [intervalEncodingSourceImpl, intervalSourceImpl, signingOracle, signingKernelOracle]
      rw [hused]
      by_cases hactive : Epoch.IsActive I ep <;>
        simp [GXMSS.Interval.scheme, GXMSS.Interval.sign, hactive, hused,
          map_eq_bind_pure_comp, bind_assoc]
    · cases hentry : state.1 ep with
      | none => exact (hused hentry).elim
      | some entry =>
        dsimp [intervalEncodingSourceImpl, intervalSourceImpl, signingOracle, signingKernelOracle]
        rw [hentry]
        simp

private theorem intervalEncodingSource_run_proj [SampleableType H] [SampleableType R]
    [DecidableEq H] (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (pk : GXMSS.PublicKey PP H) :
    Prod.map id Prod.fst <$>
      (simulateQ (intervalEncodingSourceImpl P enc K I sk) (A.forge pk)).run
        (emptyHistory, []) =
      (simulateQ (intervalSourceImpl P enc K I sk) (A.forge pk)).run emptyHistory :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (intervalEncodingSourceImpl P enc K I sk) (intervalSourceImpl P enc K I sk)
    Prod.fst (fun q state => intervalEncodingSourceImpl_proj P enc K I sk q state)
    (A.forge pk) (emptyHistory, [])

/-- This invariant concerns the auxiliary source transcript. Equality with the authoritative
encoding transcript requires accepted-query capacity and is established separately. -/
private def intervalEncodingHistoryMatches (I : Interval h)
    (history : History (Epoch h) M (GXMSS.Signature R H h v))
    (transcript : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) : Prop :=
  ∀ ep, TargetCollisionResistance.used transcript ep = true ↔
    Epoch.IsActive I ep ∧ history ep ≠ none

private theorem intervalEncodingHistoryMatches_empty (I : Interval h) :
    intervalEncodingHistoryMatches (H := H) (M := M) (R := R) (w := w) (v := v)
      I emptyHistory [] := by
  intro ep
  simp [TargetCollisionResistance.used, emptyHistory]

private theorem intervalEncodingSourceImpl_preserves_match [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (q : (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)).Domain)
    (state : History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hmatch : intervalEncodingHistoryMatches I state.1 state.2)
    (out : (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)).Range q ×
      (History (Epoch h) M (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support ((intervalEncodingSourceImpl P enc K I sk q).run state)) :
    let (_, history, transcript) := out
    intervalEncodingHistoryMatches I history transcript := by
  cases q with
  | inl uniform =>
    change out ∈ support
      ((unifSpec.query uniform : ProbComp _) >>= fun answer => pure (answer, state)) at hout
    obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
    have heq := (mem_support_pure_iff _ _).mp hreturn
    subst out
    exact hmatch
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change out ∈ support (intervalEncodingSourceImpl P enc K I sk (.inr (ep, msg))
      state) at hout
    dsimp [intervalEncodingSourceImpl] at hout
    cases hentry : state.1 ep with
    | some entry =>
      rw [hentry] at hout
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      exact hmatch
    | none =>
      rw [hentry] at hout
      by_cases hactive : Epoch.IsActive I ep
      · simp only [hactive, ite_true] at hout
        obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
        have heq := (mem_support_pure_iff _ _).mp hreturn
        subst out
        intro other
        by_cases heq : other = ep
        · subst other
          simp [TargetCollisionResistance.used, hactive, Function.update]
        · have hprev := hmatch other
          simpa [Function.update, heq, Ne.symm heq, TargetCollisionResistance.used,
            List.any_append] using hprev
      · simp only [hactive, ite_false] at hout
        have heq := (mem_support_pure_iff _ _).mp hout
        subst out
        intro other
        by_cases heq : other = ep
        · subst other
          have hprev := hmatch ep
          simp only [hactive, false_and, iff_false] at hprev
          simpa [hactive] using hprev
        · simpa [Function.update, heq] using hmatch other

private def intervalEncodingGameImpl [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) :
    QueryImpl (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v))
      (StateT (History (Epoch h) M (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) ProbComp) :=
  let completeKey := sk.complete
  let pp := completeKey.seed
  let outer := TargetCollisionResistance.oracles (encodingTCRProblem P enc qs K) pp
  (outer.mapStateTBase (intervalEncodingInnerImpl P I sk)).flattenStateT

private theorem intervalEncodingGameImpl_eq_source_of_capacity [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (q : (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)).Domain)
    (state : History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hmatch : intervalEncodingHistoryMatches I state.1 state.2)
    (hspace : let transcript := state.2
      q.isRight = true → transcript.length < qs) :
    (intervalEncodingGameImpl P enc qs K I sk q).run state =
      (intervalEncodingSourceImpl P enc K I sk q).run state := by
  cases q with
  | inl uniform =>
    change intervalEncodingGameImpl P enc qs K I sk (.inl uniform) state =
      intervalEncodingSourceImpl P enc K I sk (.inl uniform) state
    simp [intervalEncodingGameImpl, intervalEncodingInnerImpl,
      intervalEncodingSourceImpl, TargetCollisionResistance.oracles,
      QueryImpl.flattenStateT, QueryImpl.mapStateTBase]
    dsimp [StateT.mk]
    rfl
  | inr query =>
    rcases query with ⟨ep, msg⟩
    change intervalEncodingGameImpl P enc qs K I sk (.inr (ep, msg)) state =
      intervalEncodingSourceImpl P enc K I sk (.inr (ep, msg)) state
    cases hentry : state.1 ep with
    | some entry =>
      simp only [add_apply_inr, InductiveMerkleTree.range_def,
        intervalEncodingGameImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
        TargetCollisionResistance.oracles, QueryImpl.ofLift_eq_id',
        intervalEncodingInnerImpl, QueryImpl.add_apply_inr, StateT.run_mk,
        intervalEncodingSourceImpl, hentry]
      dsimp [StateT.mk]
      rw [intervalEncodingSigningOracle_used P I sk state.1 ep msg entry.1 entry.2 hentry]
      simp
    | none =>
      by_cases hactive : Epoch.IsActive I ep
      · have hfresh : TargetCollisionResistance.used state.2 ep = false :=
          Bool.eq_false_iff.mpr (fun hused => ((hmatch ep).mp hused).2 hentry)
        let transcript := state.2
        have hlen : transcript.length < qs := hspace (by simp)
        have hcap : TargetCollisionResistance.rejected qs state.2 ep = false := by
          rw [TargetCollisionResistance.rejected, hfresh, Bool.or_false,
            decide_eq_false_iff_not]
          exact Nat.not_le.mpr hlen
        simp only [add_apply_inr, InductiveMerkleTree.range_def,
          intervalEncodingGameImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          TargetCollisionResistance.oracles, QueryImpl.ofLift_eq_id', encodingTCRProblem,
          intervalEncodingInnerImpl, QueryImpl.add_apply_inr, StateT.run_mk,
          map_eq_bind_pure_comp, intervalEncodingSourceImpl, hentry, hactive, ite_true,
          bind_pure_comp]
        dsimp [StateT.mk]
        rw [intervalEncodingSigningOracle_active P I sk state.1 ep msg hentry hactive]
        simp [simulateQ_query, TargetCollisionResistance.challengeOracle,
          hcap, TargetCollisionResistance.finish,
          map_eq_bind_pure_comp, bind_assoc]
      · simp only [add_apply_inr, InductiveMerkleTree.range_def,
          intervalEncodingGameImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
          TargetCollisionResistance.oracles, QueryImpl.ofLift_eq_id',
          intervalEncodingInnerImpl, QueryImpl.add_apply_inr, StateT.run_mk,
          intervalEncodingSourceImpl, hentry, hactive, ite_false]
        dsimp [StateT.mk]
        rw [intervalEncodingSigningOracle_inactive P I sk state.1 ep msg hentry hactive]
        rfl

private theorem intervalEncodingSourceImpl_length [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (q : (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)).Domain)
    (state : History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (out : (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)).Range q ×
      (History (Epoch h) M (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support ((intervalEncodingSourceImpl P enc K I sk q).run state)) :
    let initialTranscript := state.2
    let (_, _, transcript) := out
    transcript.length ≤ initialTranscript.length + (if q matches .inr _ then 1 else 0) := by
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
    change out ∈ support (intervalEncodingSourceImpl P enc K I sk (.inr (ep, msg))
      state) at hout
    dsimp [intervalEncodingSourceImpl] at hout
    cases hentry : state.1 ep with
    | some entry =>
      rw [hentry] at hout
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      simp
    | none =>
      rw [hentry] at hout
      by_cases hactive : Epoch.IsActive I ep
      · simp only [hactive, ite_true] at hout
        obtain ⟨answer, _, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
        have heq := (mem_support_pure_iff _ _).mp hreturn
        subst out
        simp
      · simp only [hactive, ite_false] at hout
        have heq := (mem_support_pure_iff _ _).mp hout
        subst out
        simp

private theorem intervalEncodingGame_run_eq_source_of_bound {α : Type} [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (oa : OracleComp (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)) α)
    (budget : ℕ) (hbound : oa.IsQueryBoundP (fun q => q.isRight = true) budget)
    (state : History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hmatch : intervalEncodingHistoryMatches I state.1 state.2)
    (hlen : let transcript := state.2
      transcript.length + budget ≤ qs) :
    (simulateQ (intervalEncodingGameImpl P enc qs K I sk) oa).run state =
      (simulateQ (intervalEncodingSourceImpl P enc K I sk) oa).run state := by
  induction oa using OracleComp.inductionOn generalizing budget state with
  | pure value => rfl
  | query_bind q next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind]
    let transcript := state.2
    have hspace : q.isRight = true → transcript.length < qs := by
      dsimp only [transcript]
      intro hsign
      cases q with
      | inl uniform => simp at hsign
      | inr signing =>
        have hqueryBudget := hbound.1
        have hpositive : 0 < budget := hqueryBudget.resolve_left (by simp)
        omega
    rw [intervalEncodingGameImpl_eq_source_of_capacity P enc qs K I sk q state hmatch hspace]
    apply bind_congr_of_forall_mem_support
    intro output houtput
    have hmatch' := intervalEncodingSourceImpl_preserves_match P enc K I sk q
      state hmatch output houtput
    have hstep := intervalEncodingSourceImpl_length P enc K I sk q state output houtput
    have hnext : let (_, _, transcript) := output
        transcript.length +
        (if q.isRight = true then budget - 1 else budget) ≤ qs := by
      cases q with
      | inl uniform =>
        simp only [Sum.isRight, Bool.false_eq_true, ite_false] at hstep ⊢
        omega
      | inr signing =>
        simp only [Sum.isRight, ite_true] at hstep ⊢
        have hqueryBudget := hbound.1
        have hpositive : 0 < budget := hqueryBudget.resolve_left (by simp)
        omega
    exact ih output.1 (if q.isRight = true then budget - 1 else budget)
      (hbound.2 output.1) output.2 hmatch' hnext

private def intervalEncodingFirstRecordsMatch
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (state : History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) : Prop :=
  ∀ ep msg signature, state.1 ep = some (msg, signature) → Epoch.IsActive I ep →
    ∃ answer, (⟨ep, msg, answer⟩ : TargetCollisionResistance.Record M R
      (Epoch h) v (2 ^ w)) ∈ state.2 ∧
      signature = answer.map (GXMSS.Interval.signatureOfWord P I sk ep) ∧
      ∀ wr, answer = some wr →
      let completeKey := sk.complete
      enc.value completeKey.seed msg wr.2 ep = some wr.1

private theorem intervalEncodingFirstRecordsMatch_empty
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) :
    intervalEncodingFirstRecordsMatch P enc I sk (emptyHistory, []) := by
  intro ep msg signature hrecord
  simp [emptyHistory] at hrecord

private theorem intervalEncodingSourceImpl_preserves_firstRecords [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (q : (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)).Domain)
    (state : History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hinv : intervalEncodingFirstRecordsMatch P enc I sk state)
    (out : (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)).Range q ×
      (History (Epoch h) M (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support ((intervalEncodingSourceImpl P enc K I sk q).run state)) :
    intervalEncodingFirstRecordsMatch P enc I sk out.2 := by
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
    change out ∈ support (intervalEncodingSourceImpl P enc K I sk (.inr (ep, msg))
      state) at hout
    dsimp [intervalEncodingSourceImpl] at hout
    cases hentry : state.1 ep with
    | some entry =>
      rw [hentry] at hout
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      exact hinv
    | none =>
      rw [hentry] at hout
      by_cases hactive : Epoch.IsActive I ep
      · simp only [hactive, ite_true] at hout
        obtain ⟨answer, hanswer, hreturn⟩ := (mem_support_bind_iff _ _ _).mp hout
        have heq := (mem_support_pure_iff _ _).mp hreturn
        subst out
        intro other first signature hrecord hother
        by_cases heq : other = ep
        · subst other
          have hpair : first = msg ∧ signature =
              answer.map (GXMSS.Interval.signatureOfWord P I sk ep) := by
            simpa [Function.update] using hrecord.symm
          rcases hpair with ⟨hfirst, hsignature⟩
          refine ⟨answer, ?_, hsignature, ?_⟩
          · simp [hfirst]
          · intro wr hwr
            subst answer
            let completeKey := sk.complete
            simpa [hfirst] using IncomparableEncoding.Retry.value_eq_some_of_mem_retry
              enc ($ᵗ R) completeKey.seed msg ep K wr.1 wr.2 hanswer
        · have hold : state.1 other = some (first, signature) := by
            simpa [Function.update, heq] using hrecord
          obtain ⟨answer, hmem, hsig, hword⟩ := hinv other first signature hold hother
          exact ⟨answer, List.mem_append.mpr (Or.inl hmem), hsig, hword⟩
      · simp only [hactive, ite_false] at hout
        have heq := (mem_support_pure_iff _ _).mp hout
        subst out
        intro other first signature hrecord hother
        have hne : other ≠ ep := fun heq => hactive (heq ▸ hother)
        have hold : state.1 other = some (first, signature) := by
          simpa [Function.update, hne] using hrecord
        exact hinv other first signature hold hother

private theorem intervalEncodingSource_run_length {α : Type} [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (oa : OracleComp (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)) α)
    (budget : ℕ) (hbound : oa.IsQueryBoundP (fun q => q.isRight = true) budget)
    (state : History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (out : α × (History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support
      ((simulateQ (intervalEncodingSourceImpl P enc K I sk) oa).run state)) :
    let initialTranscript := state.2
    let (_, _, transcript) := out
    transcript.length ≤ initialTranscript.length + budget := by
  induction oa using OracleComp.inductionOn generalizing budget state with
  | pure value =>
    change out ∈ support (pure (value, state) : ProbComp _) at hout
    have heq := (mem_support_pure_iff _ _).mp hout
    subst out
    let initialTranscript := state.2
    change initialTranscript.length ≤ initialTranscript.length + budget
    omega
  | query_bind q next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind] at hout
    obtain ⟨output, houtput, hrest⟩ := (mem_support_bind_iff _ _ _).mp hout
    have hstep := intervalEncodingSourceImpl_length P enc K I sk q state output houtput
    have hfinal := ih output.1 (if q.isRight = true then budget - 1 else budget)
      (hbound.2 output.1) output.2 hrest
    rcases output with ⟨answer, history, transcript⟩
    dsimp only at hstep hfinal ⊢
    cases q with
    | inl uniform =>
      simp only [Sum.isRight, Bool.false_eq_true, ite_false] at hstep hfinal
      omega
    | inr signing =>
      simp only [Sum.isRight, ite_true] at hstep hfinal
      have hqueryBudget := hbound.1
      have hpositive : 0 < budget := hqueryBudget.resolve_left (by simp)
      omega

/-- All three assertions concern the actual accepted challenge history under the pathwise
bound on every signing request, including inactive, failed and repeated requests. -/
private theorem intervalEncodingGame_run_records {α : Type} [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (oa : OracleComp (unifSpec + signingSpec (Epoch h) M (GXMSS.Signature R H h v)) α)
    (hbound : oa.IsQueryBoundP (fun q => q.isRight = true) qs)
    (out : α × (History (Epoch h) M (GXMSS.Signature R H h v) ×
      TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)))
    (hout : out ∈ support
      ((simulateQ (intervalEncodingGameImpl P enc qs K I sk) oa).run (emptyHistory, []))) :
    let (_, history, transcript) := out
    intervalEncodingHistoryMatches I history transcript ∧
      intervalEncodingFirstRecordsMatch P enc I sk (history, transcript) ∧
      transcript.length ≤ qs := by
  rw [intervalEncodingGame_run_eq_source_of_bound P enc qs K I sk oa qs hbound
    (emptyHistory, []) (intervalEncodingHistoryMatches_empty I) (by simp)] at hout
  refine ⟨?_, ?_, ?_⟩
  · exact OracleComp.simulateQ_run_preservesInv (intervalEncodingSourceImpl P enc K I sk)
      (fun state => intervalEncodingHistoryMatches I state.1 state.2)
      (fun q state hstate answer hans =>
        intervalEncodingSourceImpl_preserves_match P enc K I sk q state hstate answer hans)
      oa (emptyHistory, []) (intervalEncodingHistoryMatches_empty I) out hout
  · exact OracleComp.simulateQ_run_preservesInv (intervalEncodingSourceImpl P enc K I sk)
      (intervalEncodingFirstRecordsMatch P enc I sk)
      (fun q state hstate answer hans =>
        intervalEncodingSourceImpl_preserves_firstRecords P enc K I sk q state hstate answer hans)
      oa (emptyHistory, []) (intervalEncodingFirstRecordsMatch_empty P enc I sk) out hout
  · simpa using intervalEncodingSource_run_length P enc K I sk oa qs hbound
      (emptyHistory, []) out hout

private noncomputable def intervalEncodingSourceProgram
    [SampleableType H] [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v)) :
    ProbComp (ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) := do
  let thf := P.thf
  let pp ← thf.seedGen
  let starts ← GXMSS.sampleStarts H h v
  let fillers ← GXMSS.IntervalMerkle.sampleFillers I H
  let (pk, sk) := GXMSS.Interval.keys P I pp starts fillers
  let (forgery, state) ←
    (simulateQ (intervalEncodingSourceImpl P enc K I sk) (A.forge pk)).run (emptyHistory, [])
  pure ((pk, forgery, state.1), state.2)

private theorem intervalEncodingSourceProgram_proj
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v)) :
    Prod.fst <$> intervalEncodingSourceProgram P enc K I A = (do
      let (pk, sk) ← GXMSS.Interval.keygen P I
      GXMSS.Interval.viewWithKeys P enc K I A pk sk) := by
  simp only [intervalEncodingSourceProgram, GXMSS.Interval.keygen, map_bind, map_pure,
    bind_assoc, pure_bind]
  congr 1
  funext pp
  congr 1
  funext starts
  congr 1
  funext fillers
  let keys := GXMSS.Interval.keys P I pp starts fillers
  have hproj := congrArg
    (fun c => (fun z => ((keys.1, z.1, z.2) :
      ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))) <$> c)
    (intervalEncodingSource_run_proj P enc K I keys.2 A keys.1)
  simpa only [keys, ExperimentResult, intervalSourceImpl, GXMSS.Interval.viewWithKeys,
    runWithSigningOracle, runWithSigningKernel, oraclesWithSigningKernel, signingOracle,
    Functor.map_map,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq] using hproj

private theorem intervalEncodingOuter_lift {α : Type} [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (pp : PP) (c : ProbComp α)
    (transcript : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) :
    (simulateQ (TargetCollisionResistance.oracles (encodingTCRProblem P enc qs K) pp)
      (OracleComp.liftComp c (unifSpec + TargetCollisionResistance.challengeSpec
        M R (Epoch h) v (2 ^ w)))).run transcript =
      (fun x => (x, transcript)) <$> c := by
  simp [TargetCollisionResistance.oracles, QueryImpl.simulateQ_add_liftM_left,
    simulateQ_liftTarget]

private theorem intervalEncodingNested_run_eq_source [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (hbound : SigningQueryBound qs A)
    (pp : PP) (starts : Epoch h → Fin v → H) (fillers : Fillers I H) :
    let keys := GXMSS.Interval.keys P I pp starts fillers
    (simulateQ (TargetCollisionResistance.oracles (encodingTCRProblem P enc qs K) pp)
      ((simulateQ (intervalEncodingInnerImpl P I keys.2) (A.forge keys.1)).run
        emptyHistory)).run ([] : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) =
      (fun (value, history, transcript) => ((value, history), transcript)) <$>
        (simulateQ (intervalEncodingSourceImpl P enc K I keys.2) (A.forge keys.1)).run
          (emptyHistory, []) := by
  dsimp
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun (value, history, transcript) => ((value, history), transcript)) <$>
    (simulateQ (intervalEncodingGameImpl P enc qs K I
      (GXMSS.Interval.keys P I pp starts fillers).2)
      (A.forge (GXMSS.Interval.keys P I pp starts fillers).1)).run (emptyHistory, []) = _
  exact congrArg
    (fun c => (fun (value, history, transcript) => ((value, history), transcript)) <$> c)
    (intervalEncodingGame_run_eq_source_of_bound P enc qs K I
      (GXMSS.Interval.keys P I pp starts fillers).2
      (A.forge (GXMSS.Interval.keys P I pp starts fillers).1) qs
      (hbound (GXMSS.Interval.keys P I pp starts fillers).1) (emptyHistory, [])
      (intervalEncodingHistoryMatches_empty I) (by simp))

private noncomputable def intervalEncodingTargetTail [DecidableEq M] [DecidableEq R]
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w)) : ProbComp Bool :=
  let ((pk, (epoch, message, signature), _history), transcript) := out
  pure (TargetCollisionResistance.valid enc pk.seed transcript
    (message, signature.randomizer, epoch))

/-- The original primitive experiment is exactly the joint source computation and its
accepted target transcript. Missing mass and all returned candidate outputs are retained. -/
private theorem intervalEncodingTargetExperiment_eq_coupled
    [SampleableType H] [SampleableType R] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (hbound : SigningQueryBound qs A) :
    TargetCollisionResistance.experiment (encodingTargetCollisionReduction P enc qs K I A) =
      intervalEncodingSourceProgram P enc K I A >>= intervalEncodingTargetTail enc := by
  unfold TargetCollisionResistance.experiment encodingTargetCollisionReduction
  unfold intervalEncodingSourceProgram intervalEncodingTargetTail
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]
  simp only [intervalEncodingOuter_lift]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  let thf := P.thf
  apply congrArg (fun (f : PP → ProbComp Bool) => thf.seedGen >>= f)
  funext pp
  apply congrArg (fun (f : (Epoch h → Fin v → H) → ProbComp Bool) =>
    GXMSS.sampleStarts H h v >>= f)
  funext starts
  apply congrArg (fun (f : Fillers I H → ProbComp Bool) =>
    GXMSS.IntervalMerkle.sampleFillers I H >>= f)
  funext fillers
  rw [intervalEncodingNested_run_eq_source P enc qs K I A hbound pp starts fillers]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

private noncomputable def intervalEncodingCollision [DecidableEq M] [DecidableEq R]
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (I : Interval h)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v)) :
    Bool :=
  let (pk, (epoch, message, signature), history) := out
  if Epoch.IsActive I epoch then
    match history epoch with
    | some (first, some honestSignature) =>
      match enc.value pk.seed first honestSignature.randomizer epoch,
        enc.value pk.seed message signature.randomizer epoch with
      | some honestWord, some candidateWord =>
        decide (honestWord = candidateWord ∧
          (first, honestSignature.randomizer) ≠ (message, signature.randomizer))
      | _, _ => false
    | _ => false
  else false

private theorem intervalEncodingCollision_valid
    [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (transcript : TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hseed : let (pk, _, _) := out
      let complete := sk.complete
      pk.seed = complete.seed)
    (hrecords : let (_, _, history) := out
      intervalEncodingFirstRecordsMatch P enc I sk (history, transcript))
    (hcollision : intervalEncodingCollision enc I out = true) :
    let (_, (epoch, message, signature), _) := out
    let completeKey := sk.complete
    TargetCollisionResistance.valid enc completeKey.seed transcript
      (message, signature.randomizer, epoch) = true := by
  rcases out with ⟨pk, ⟨epoch, message, signature⟩, history⟩
  let completeKey := sk.complete
  let pp := completeKey.seed
  dsimp only [intervalEncodingCollision] at hcollision
  by_cases hactive : Epoch.IsActive I epoch
  · simp only [hactive, ite_true] at hcollision
    cases hentry : history epoch with
    | none => simp [hentry] at hcollision
    | some entry =>
      rcases entry with ⟨first, answer⟩
      cases answer with
      | none => simp [hentry] at hcollision
      | some honestSignature =>
        simp only [hentry] at hcollision
        cases hhonest : enc.value pk.seed first honestSignature.randomizer epoch with
        | none => simp [hhonest] at hcollision
        | some honestWord =>
          cases hforged : enc.value pk.seed message signature.randomizer epoch with
          | none => simp [hhonest, hforged] at hcollision
          | some candidateWord =>
            have hpair : honestWord = candidateWord ∧
                (first, honestSignature.randomizer) ≠ (message, signature.randomizer) := by
              simpa only [hhonest, hforged, decide_eq_true_eq] using hcollision
            obtain ⟨record, hmem, hsignature, hvalue⟩ :=
              hrecords epoch first (some honestSignature) hentry hactive
            cases record with
            | none => simp at hsignature
            | some wr =>
              have hsig : honestSignature = GXMSS.Interval.signatureOfWord P I sk epoch wr :=
                Option.some.inj hsignature
              have hr : honestSignature.randomizer = wr.2 := by rw [hsig]; rfl
              have hword : honestWord = wr.1 := by
                have hresult := hvalue wr rfl
                rw [show pk.seed = pp from hseed, hr, hresult] at hhonest
                exact (Option.some.inj hhonest).symm
              have hv : enc.value pp message signature.randomizer epoch = some wr.1 := by
                simpa only [show pk.seed = pp from hseed,
                  ← hpair.1, hword] using hforged
              have hn : (first, wr.2) ≠ (message, signature.randomizer) := by
                simpa only [hr] using hpair.2
              change TargetCollisionResistance.valid enc pp transcript
                (message, signature.randomizer, epoch) = true
              simp only [TargetCollisionResistance.valid, hv]
              apply List.any_eq_true.mpr
              refine ⟨⟨epoch, first, some (wr.1, wr.2)⟩, hmem, ?_⟩
              simp [hn]
  · simp [hactive] at hcollision

private theorem intervalEncodingSourceProgram_collision_tail
    [SampleableType H] [SampleableType R] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v) ×
        TargetCollisionResistance.Transcript M R (Epoch h) v (2 ^ w))
    (hout : out ∈ support (intervalEncodingSourceProgram P enc K I A))
    (hcollision : intervalEncodingCollision enc I out.1 = true) :
    intervalEncodingTargetTail enc out = pure true := by
  unfold intervalEncodingSourceProgram at hout
  obtain ⟨pp, _, hrest⟩ := support_bind_exists hout
  obtain ⟨starts, _, hrest⟩ := support_bind_exists hrest
  obtain ⟨fillers, _, hrest⟩ := support_bind_exists hrest
  obtain ⟨runout, hrun, hret⟩ := support_bind_exists hrest
  have heq := (mem_support_pure_iff _ _).mp hret
  subst out
  let keys := GXMSS.Interval.keys P I pp starts fillers
  have hrecords := OracleComp.simulateQ_run_preservesInv
    (intervalEncodingSourceImpl P enc K I keys.2)
    (intervalEncodingFirstRecordsMatch P enc I keys.2)
    (fun q state hstate answer hans =>
      intervalEncodingSourceImpl_preserves_firstRecords P enc K I keys.2 q state
        hstate answer hans)
    (A.forge keys.1) (emptyHistory, [])
    (intervalEncodingFirstRecordsMatch_empty P enc I keys.2) runout hrun
  rcases runout with ⟨forgery, history, transcript⟩
  have hvalid := intervalEncodingCollision_valid P enc I keys.2
    (keys.1, forgery, history) transcript rfl hrecords hcollision
  rcases forgery with ⟨epoch, message, signature⟩
  simpa only [intervalEncodingTargetTail, keys, GXMSS.Interval.keys, GXMSS.keys]
    using congrArg pure hvalid

/-- Native returned encoding-collision mass is bounded by the advantage of
`encodingTargetCollisionReduction`, using its accepted transcript and the all-request query
bound. -/
private theorem intervalEncodingCollisionMass_le_advantage
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (hbound : SigningQueryBound qs A) :
    ProbCompRuntime.probComp.evalDist (do
      let (pk, sk) ← GXMSS.Interval.keygen P I
      let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
      pure (intervalEncodingCollision enc I out)) {true} ≤
      TargetCollisionResistance.advantage (encodingTargetCollisionReduction P enc qs K I A) := by
  have hprogram : (do
      let (pk, sk) ← GXMSS.Interval.keygen P I
      let out ← GXMSS.Interval.viewWithKeys P enc K I A pk sk
      pure (intervalEncodingCollision enc I out)) =
      (fun z => intervalEncodingCollision enc I z.1) <$>
        intervalEncodingSourceProgram P enc K I A := by
    have hproj := congrArg (fun c => intervalEncodingCollision enc I <$> c)
      (intervalEncodingSourceProgram_proj P enc K I A)
    simpa only [map_bind, map_pure, Functor.map_map, Function.comp_def,
      map_eq_bind_pure_comp, bind_assoc, pure_bind] using hproj.symm
  unfold TargetCollisionResistance.advantage TargetCollisionResistance.outputMeasure
  rw [hprogram, intervalEncodingTargetExperiment_eq_coupled P enc qs K I A hbound]
  simp only [map_eq_bind_pure_comp, Function.comp_def, ProbCompRuntime.probComp_evalDist]
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (intervalEncodingSourceProgram P enc K I A)
    (fun z => pure (intervalEncodingCollision enc I z.1))
    (intervalEncodingTargetTail enc) (measurableSet_singleton true)
  intro out hout
  by_cases hcollision : intervalEncodingCollision enc I out.1 = true
  · rw [intervalEncodingSourceProgram_collision_tail P enc K I A out hout hcollision]
    simp [hcollision]
  · have hfalse : intervalEncodingCollision enc I out.1 = false := by
      cases hvalue : intervalEncodingCollision enc I out.1 <;> simp_all
    simp [hfalse]

end GXMSS.Interval.Reductions
