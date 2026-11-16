/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionReduction.Basic
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# Encoding collision oracle simulation

Coupled source and hash histories agree throughout adaptive interaction. Program equalities
retain returned exhaustion and every occupied slot without conditioning on termination.
-/

public section

namespace IncomparableEncoding.TargetCollisionReduction

open OracleComp OracleSpec TargetCollisionResistance TweakableHash

variable {PP M R E Tweak Y : Type} {n radix : ℕ}

/-- Each source challenge query is forwarded to the corresponding hash challenge and its returned
word is lifted. Recording through `finish` retains rejected queries and exhausted entries. -/
@[expose] def challengeLift [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p : ℕ) :
    QueryImpl (TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix)
        (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))) := fun q => do
  let targetAnswer ← liftM ((unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y).query
    (.inr (bridge.epochToTweak q.2, q.1)))
  let answer := targetAnswer.map fun pair => (bridge.word pair.1, pair.2)
  modify fun s => (TargetCollisionResistance.finish p s q.1 q.2 answer).2
  return answer

/-- Private random queries pass through unchanged; challenge queries use `challengeLift`. -/
@[expose] def liftedOracles [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p : ℕ) :
    QueryImpl (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix)
        (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))) :=
  (QueryImpl.ofLift unifSpec
    (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))).liftTarget
      (StateT (TargetCollisionResistance.Transcript M R E n radix)
        (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))) +
    challengeLift bridge p

/-- Flattening the nested source and hash challenge handlers exposes both ordered histories. -/
@[expose] noncomputable def coupledOracles [DecidableEq E] [DecidableEq Tweak]
    [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP) :
    QueryImpl (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp) :=
  ((SM_DT_RTCR_oracles (hashProblem bridge p K) pp).mapStateTBase
    (liftedOracles bridge p)).flattenStateT

/-- A direct coupled source handler mirrors the encoding challenge and records the corresponding
hash target. The second history remains a projection of the first. -/
@[expose] def sourceCoupledChallenge [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP) :
    QueryImpl (TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp) := fun q => do
  let state ← get
  let transcript := state.1
  if TargetCollisionResistance.rejected p transcript q.2 then return none
  else
    let answer ← ((bridge.enc.retry ($ᵗ R) pp q.1 q.2 K :
      ProbComp (Option (Codeword n radix × R))) :
      StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp (Option (Codeword n radix × R)))
    let entry : TargetCollisionResistance.Record M R E n radix := ⟨q.2, q.1, answer⟩
    set (transcript ++ [entry], state.2 ++ [targetRecord bridge entry])
    return answer

/-- Private random draws have the same meaning in the direct coupled source game. -/
@[expose] def sourceCoupledOracles [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP) :
    QueryImpl (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) ProbComp) +
    sourceCoupledChallenge bridge p K pp

/-- The source record word and hash history agree with the pinned target game. -/
@[expose] def CoupledInv (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) : Prop :=
  state.2 = targetHistory bridge state.1 ∧ WellFormed bridge pp state.1

/-- The two histories start empty and agree. -/
theorem coupledInv_empty (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP) :
    CoupledInv bridge pp ([], []) := by
  constructor
  · rfl
  · simp [WellFormed]

/-- Under the history relation, one source query and its hash simulation have identical
returned values and next states. -/
theorem coupledOracles_eq_sourceCoupled_of_inv
    [DecidableEq E] [DecidableEq Tweak] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Domain)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state) :
    (coupledOracles bridge p K pp q).run state =
      (sourceCoupledOracles bridge p K pp q).run state := by
  cases q with
  | inl random =>
      have hsimple :
          (fun answer => (answer.1, state.1, answer.2)) <$>
            (SM_DT_RTCR_oracles (hashProblem bridge p K) pp (.inl random)).run state.2 =
          (fun answer => (answer, state)) <$> (unifSpec.query random : ProbComp _) := by
        simp [SM_DT_RTCR_oracles, QueryImpl.ofLift_eq_id']
      change (fun answer => (answer.1, state.1, answer.2)) <$>
          (SM_DT_RTCR_oracles (hashProblem bridge p K) pp (.inl random)).run state.2 =
        (fun answer => (answer, state)) <$> (unifSpec.query random : ProbComp _)
      exact hsimple
  | inr query =>
      rcases query with ⟨msg, ep⟩
      have hreject :
          (p ≤ state.2.length ∨
            TweakReserved Prod.fst state.2 (bridge.epochToTweak ep)) ↔
            TargetCollisionResistance.rejected p state.1 ep = true := by
        rw [hinv.1, ← rejected_iff_target_rejected bridge p state.1 ep]
      by_cases h : TargetCollisionResistance.rejected p state.1 ep = true
      · have ht := hreject.mpr h
        simp [coupledOracles, liftedOracles, challengeLift, sourceCoupledOracles,
          sourceCoupledChallenge, SM_DT_RTCR_oracles, SM_DT_RTCR_challengeOracle,
          QueryImpl.mapStateTBase, QueryImpl.flattenStateT, h, ht,
          TargetCollisionResistance.finish, hashProblem]
      · have ht : ¬ (p ≤ state.2.length ∨
            TweakReserved Prod.fst state.2 (bridge.epochToTweak ep)) := by
          intro ht
          exact h (hreject.mp ht)
        have hsimple :
            (fun answer : Option (Y × R) =>
              (answer.map fun pair => (bridge.word pair.1, pair.2),
                state.1 ++ [⟨ep, msg, answer.map fun pair => (bridge.word pair.1, pair.2)⟩],
                state.2 ++ [(bridge.epochToTweak ep, msg, answer.map Prod.snd)])) <$>
              SM_DT_RTCR_resample (hashProblem bridge p K) pp
                (bridge.epochToTweak ep) msg K =
            (fun answer : Option (Codeword n radix × R) =>
              (answer, state.1 ++ [⟨ep, msg, answer⟩],
                state.2 ++ [targetRecord bridge ⟨ep, msg, answer⟩])) <$>
              bridge.enc.retry ($ᵗ R) pp msg ep K := by
          rw [retry_eq_resample bridge p K pp msg ep]
          simp only [PFunctor.FreeM.map_eq_map, Functor.map_map,
            hashProblem, targetRecord]
          simp [Option.map_map, Function.comp_def]
        simpa [coupledOracles, liftedOracles, challengeLift, sourceCoupledOracles,
          sourceCoupledChallenge, SM_DT_RTCR_oracles, SM_DT_RTCR_challengeOracle,
          QueryImpl.mapStateTBase, QueryImpl.flattenStateT, h, ht,
          TargetCollisionResistance.finish, hashProblem] using hsimple

/-- The direct challenge handler maintains history alignment and full-word correctness on every
returned path. Missing execution mass contributes no path and is left unchanged. -/
theorem sourceCoupledChallenge_preserves_inv [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : M × E)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state)
    (out : Option (Codeword n radix × R) ×
      (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R))
    (hout : out ∈ support ((sourceCoupledChallenge bridge p K pp q).run state)) :
    CoupledInv bridge pp out.2 := by
  rcases q with ⟨msg, ep⟩
  by_cases hreject : TargetCollisionResistance.rejected p state.1 ep = true
  · have hrun : (sourceCoupledChallenge bridge p K pp (msg, ep)).run state =
        pure (none, state) := by simp [sourceCoupledChallenge, hreject]
    rw [hrun] at hout
    have heq := (mem_support_pure_iff _ _).mp hout
    subst out
    exact hinv
  · have hrun : (sourceCoupledChallenge bridge p K pp (msg, ep)).run state =
        bridge.enc.retry ($ᵗ R) pp msg ep K >>= fun answer =>
          pure (answer, (state.1 ++ [⟨ep, msg, answer⟩],
            state.2 ++ [targetRecord bridge ⟨ep, msg, answer⟩])) := by
      simp [sourceCoupledChallenge, hreject]
    rw [hrun] at hout
    obtain ⟨answer, hanswer, hreturned⟩ := (mem_support_bind_iff _ _ _).mp hout
    have heq := (mem_support_pure_iff _ _).mp hreturned
    subst out
    constructor
    · simp [hinv.1, targetHistory]
    · intro entry hmem word r hresult
      rcases List.mem_append.mp hmem with hold | hnew
      · exact hinv.2 entry hold word r hresult
      · have hentry : entry = (⟨ep, msg, answer⟩ :
            TargetCollisionResistance.Record M R E n radix) := by
          simpa using hnew
        subst entry
        have hanswer' : answer = some (word, r) := hresult
        subst answer
        exact word_eq_of_mem_retry bridge pp msg ep K word r hanswer

/-- Ordinary random draws leave both histories alone; the challenge case uses the preceding
invariant lemma. -/
theorem sourceCoupledOracles_preserves_inv [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Domain)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state)
    (out : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Range q ×
      (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R))
    (hout : out ∈ support ((sourceCoupledOracles bridge p K pp q).run state)) :
    CoupledInv bridge pp out.2 := by
  cases q with
  | inl random =>
      have hrun : (sourceCoupledOracles bridge p K pp (.inl random)).run state =
          (fun answer => (answer, state)) <$> (unifSpec.query random : ProbComp _) := by
        rfl
      rw [hrun] at hout
      simp only [support_map, Set.mem_image] at hout
      obtain ⟨answer, _, heq⟩ := hout
      subst out
      exact hinv
  | inr query =>
      exact sourceCoupledChallenge_preserves_inv bridge p K pp query state hinv out hout

/-- Adaptive source and target simulations agree on the full paired state from an aligned
starting point. The theorem is an equality of partial computations, so returned failure and
unreturned mass are retained. -/
theorem coupled_run_eq_source [DecidableEq E] [DecidableEq Tweak] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state) :
    (simulateQ (coupledOracles bridge p K pp) program).run state =
      (simulateQ (sourceCoupledOracles bridge p K pp) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map, StateT.run_bind]
      rw [coupledOracles_eq_sourceCoupled_of_inv bridge p K pp q state hinv]
      apply bind_congr_of_forall_mem_support
      intro output houtput
      exact ih output.1 output.2
        (sourceCoupledOracles_preserves_inv bridge p K pp q state hinv output houtput)

/-- Forgetting the target history gives exactly the source challenge handler. -/
theorem sourceCoupledOracles_proj [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Domain)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) :
    Prod.map id Prod.fst <$> (sourceCoupledOracles bridge p K pp q).run state =
      (TargetCollisionResistance.oracles (encodingProblem bridge p K) pp q).run state.1 := by
  cases q with
  | inl random =>
      simp [sourceCoupledOracles, TargetCollisionResistance.oracles]
  | inr query =>
      rcases query with ⟨msg, ep⟩
      by_cases h : TargetCollisionResistance.rejected p state.1 ep = true
      · simp [sourceCoupledOracles, sourceCoupledChallenge,
          TargetCollisionResistance.oracles, TargetCollisionResistance.challengeOracle,
          encodingProblem, h]
      · simp [sourceCoupledOracles, sourceCoupledChallenge,
          TargetCollisionResistance.oracles, TargetCollisionResistance.challengeOracle,
          encodingProblem, h, TargetCollisionResistance.finish]

/-- Source simulation is the first projection of the direct paired simulation. -/
theorem sourceCoupled_run_proj [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) :
    Prod.map id Prod.fst <$> (simulateQ (sourceCoupledOracles bridge p K pp) program).run state =
      (simulateQ (TargetCollisionResistance.oracles (encodingProblem bridge p K) pp)
        program).run state.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (sourceCoupledOracles bridge p K pp)
    (TargetCollisionResistance.oracles (encodingProblem bridge p K) pp)
    Prod.fst (sourceCoupledOracles_proj bridge p K pp) program state

/-- Every returned path of an adaptive source adversary retains the coupled history invariant. -/
theorem sourceCoupled_run_preserves_inv [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state)
    (out : α × (TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R))
    (hout : out ∈ support ((simulateQ (sourceCoupledOracles bridge p K pp) program).run state)) :
    CoupledInv bridge pp out.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      exact hinv
  | query_bind q next ih =>
      have hbind : out ∈ support
          (((sourceCoupledOracles bridge p K pp q).run state) >>= fun result =>
            (simulateQ (sourceCoupledOracles bridge p K pp) (next result.1)).run result.2) := by
        simpa [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, StateT.run_bind] using hout
      obtain ⟨result, hstep, hrest⟩ := (mem_support_bind_iff _ _ _).mp hbind
      exact ih result.1 result.2
        (sourceCoupledOracles_preserves_inv bridge p K pp q state hinv result hstep)
        hrest

/-- Flattening the hash game around the source adversary yields the same coupled program from
empty histories. This equality includes both histories and every returned failure. -/
theorem nested_run_eq_source [DecidableEq E] [DecidableEq Tweak] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α) :
    (simulateQ (SM_DT_RTCR_oracles (hashProblem bridge p K) pp)
      ((simulateQ (liftedOracles bridge p) program).run [])).run
        ([] : SM_DT_RTCR_State Tweak M R) =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceCoupledOracles bridge p K pp) program).run ([], []) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun result => ((result.1, result.2.1), result.2.2)) <$>
      (simulateQ (coupledOracles bridge p K pp) program).run ([], []) = _
  rw [coupled_run_eq_source bridge p K pp program ([], [])
    (coupledInv_empty bridge pp)]

end IncomparableEncoding.TargetCollisionReduction
