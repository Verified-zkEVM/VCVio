/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.Interval.FillerOpening
import all HashSig.GXMSS.Security.Auxiliary.Interval.FillerOpening
public import HashSig.GXMSS.Security.Auxiliary.Interval.FillerTargets
import all HashSig.GXMSS.Security.Auxiliary.Interval.FillerTargets
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD

/-!
# Adaptive interval filler reductions
-/

public section

namespace GXMSS.Interval.Filler

open GXMSS.IntervalMerkle GXMSS.Interval.MerkleWitnesses GXMSS.Interval SyncSignatureUnforgeability
open OracleSpec OracleComp TweakableHash Encoding

variable {PP T X H M R : Type} {h w v : ℕ}

/-- Standalone undetectability for the original hash and selected input embedding. -/
@[expose, reducible] noncomputable def udProblem [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family) :
    SM_DT_UD_Problem Empty PP T X (Input f H v) H :=
  .standalone P.thf (embed P f) (embed P f).injective
    ($ᵗ Input f H v) ($ᵗ H) (targetCapacity f I)

/-- Standalone preimage resistance for the original hash and selected input embedding. -/
@[expose, reducible] def preProblem (P : HashInstance PP T X H h w v)
    (I : Interval h) (f : Family) :
    SM_DT_PRE_Problem Empty PP T X (Input f H v) H :=
  .standalone P.thf (embed P f) (embed P f).injective (targetCapacity f I)


/-- Seed-independent challenge phase; refusal stops setup without inventing an answer. -/
private def collectTargets (P : HashInstance PP T X H h w v) (f : Family) (I : Interval h) :
    List (Target f I) → OracleComp
      (unifSpec + (SM_DT_UD_challengeSpec T H + collectionSpec (.empty PP T H)))
      (Option (List H))
  | [] => pure (some [])
  | n :: ns => do
      let answer ← liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
        collectionSpec (.empty PP T H))).query (.inr (.inl (tweak P n))))
      match answer with
      | none => pure none
      | some digest => do
          let rest ← collectTargets P f I ns
          pure (rest.map (digest :: ·))

/-- Explicit independent response sampler in issue order, before any adaptive continuation. -/
private noncomputable def sampleResponses [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (world : SM_DT_UD_World) (pp : PP) : List (Target f I) → ProbComp (List H)
  | [] => pure []
  | n :: ns => do
      let answer ← SM_DT_UD_response world (udProblem P I f) pp (tweak P n)
      let rest ← sampleResponses P I f world pp ns
      pure (answer :: rest)

/-- The pinned UD handler at the common empty-collection registration signature. -/
private noncomputable def udOracle [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (world : SM_DT_UD_World) (pp : PP) :
    QueryImpl (unifSpec + (SM_DT_UD_challengeSpec T H + collectionSpec (.empty PP T H)))
      (StateT (SM_DT_UD_State T) ProbComp) :=
  SM_DT_UD_oracles world (udProblem P I f) pp

/-- The pinned PRE handler at the same empty-collection registration signature. -/
private noncomputable def preOracle [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family) (pp : PP) :
    QueryImpl (unifSpec + (SM_DT_UD_challengeSpec T H + collectionSpec (.empty PP T H)))
      (StateT (SM_DT_PRE_State T (Input f H v)) ProbComp) :=
  SM_DT_PRE_oracles (preProblem P I f) pp

private theorem collect_query_ud [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (world : SM_DT_UD_World) (pp : PP) (t : T) (state : SM_DT_UD_State T) :
    (simulateQ (udOracle P I f world pp)
      (liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
        collectionSpec (.empty PP T H))).query (.inr (.inl t))))).run state =
      (SM_DT_UD_challengeOracle world (udProblem P I f) pp t).run state := by
  dsimp only [udOracle, udProblem, SM_DT_UD_Problem.standalone]
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_query_right, QueryImpl.add_apply_inl]

/-- The complete joint collector law retains all answers and the accepted history in issue order.
Its hypotheses ensure every submitted target is accepted; refusal draws are never discarded. -/
private theorem collectTargets_run_ud [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (world : SM_DT_UD_World) (pp : PP) (nodes : List (Target f I))
    (issued : List T) (hnd : nodes.Nodup)
    (hfresh : ∀ n ∈ nodes, tweak P n ∉ issued)
    (hcap : issued.length + nodes.length ≤ targetCapacity f I) :
    (simulateQ (udOracle P I f world pp)
      (collectTargets P f I nodes)).run (issued, []) =
      (do
        let answers ← sampleResponses P I f world pp nodes
        pure (some answers, (issued ++ nodes.map (tweak P), []))) := by
  induction nodes generalizing issued with
  | nil => simp [collectTargets, sampleResponses, simulateQ_pure]
  | cons n ns ih =>
    have hlen : issued.length < (udProblem P I f).numTargets := by
      simpa [udProblem, SM_DT_UD_Problem.standalone] using
        (show issued.length < targetCapacity f I by simp only [List.length_cons] at hcap; omega)
    have htfresh : TweakFresh id issued [] (tweak P n) := by
      simpa [TweakFresh, TweakReserved] using hfresh n (by simp)
    have hquery : (SM_DT_UD_challengeOracle world (udProblem P I f) pp (tweak P n)).run
        (issued, []) = (fun y => (some y, (issued ++ [tweak P n], []))) <$>
          SM_DT_UD_response world (udProblem P I f) pp (tweak P n) := by
      cases world with
      | real => simpa [SM_DT_UD_response, map_eq_bind_pure_comp, monad_norm] using
          (SM_DT_UD_challengeOracle_run_of_fresh_real (pk := pp) hlen htfresh)
      | ideal => exact SM_DT_UD_challengeOracle_run_of_fresh_ideal hlen htfresh
    have htail : ∀ m ∈ ns, tweak P m ∉ issued ++ [tweak P n] := by
      intro m hm
      simp only [List.mem_append, List.mem_singleton, not_or]
      refine ⟨hfresh m (by simp [hm]), ?_⟩
      intro heq
      have hmn := tweak_injective P f I heq
      exact (List.nodup_cons.mp hnd).1 (hmn ▸ hm)
    have htailcap : (issued ++ [tweak P n]).length + ns.length ≤ targetCapacity f I := by
      simp only [List.length_append, List.length_singleton] at *
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap
    simp only [collectTargets, simulateQ_bind, StateT.run_bind]
    rw [collect_query_ud, hquery]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    simp only [sampleResponses, bind_assoc]
    apply bind_congr
    intro answer
    simp only [simulateQ_bind, StateT.run_bind]
    rw [ih (issued ++ [tweak P n]) (List.nodup_cons.mp hnd).2 htail htailcap]
    simp [monad_norm, List.append_assoc]

/-- Starting empty, every enumerated challenge is accepted and the exact target history is kept. -/
private theorem collectTargets_run_ud_empty [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (world : SM_DT_UD_World) (pp : PP) :
    (simulateQ (udOracle P I f world pp)
      (collectTargets P f I (targetList f I))).run ([], []) =
      (do
        let answers ← sampleResponses P I f world pp (targetList f I)
        pure (some answers, ((targetList f I).map (tweak P), []))) := by
  simpa using collectTargets_run_ud P I f world pp (targetList f I) []
    (targetList_nodup f I) (by simp) (by simp)

/-- PRE's explicit hidden input transcript, retaining original target tweaks in issue order. -/
private noncomputable def sampleHiddenInputs [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family) :
    List (Target f I) → ProbComp (List (T × Input f H v))
  | [] => pure []
  | n :: ns => do
      let input ← $ᵗ Input f H v
      let rest ← sampleHiddenInputs P I f ns
      pure ((tweak P n, input) :: rest)

/-- Public images corresponding to the retained hidden PRE transcript. -/
private def hiddenImages (P : HashInstance PP T X H h w v) (f : Family) (pp : PP)
    (hidden : List (T × Input f H v)) : List H :=
  hidden.map (fun (t, input) => TweakableHash.eval P.thf pp t (embed P f input))

private theorem collect_query_pre [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (pp : PP) (t : T) (state : SM_DT_PRE_State T (Input f H v)) :
    (simulateQ (preOracle P I f pp)
      (liftM ((unifSpec + (SM_DT_UD_challengeSpec T H +
        collectionSpec (.empty PP T H))).query (.inr (.inl t))))).run state =
      (SM_DT_PRE_challengeOracle (preProblem P I f) pp t).run state := by
  dsimp only [preOracle, preProblem, SM_DT_PRE_Problem.standalone]
  rw [SM_DT_PRE_oracles, QueryImpl.simulateQ_add_query_right, QueryImpl.add_apply_inl]

/-- The complete PRE collector law retains hidden inputs as well as all public responses.
The adversary receives only the response projection of this joint transcript. -/
private theorem collectTargets_run_pre [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (pp : PP) (nodes : List (Target f I)) (issued : List (T × Input f H v))
    (hnd : nodes.Nodup) (hfresh : ∀ n ∈ nodes, tweak P n ∉ issued.map Prod.fst)
    (hcap : issued.length + nodes.length ≤ targetCapacity f I) :
    (simulateQ (preOracle P I f pp)
      (collectTargets P f I nodes)).run (issued, []) =
      (do
        let hidden ← sampleHiddenInputs P I f nodes
        pure (some (hiddenImages P f pp hidden), (issued ++ hidden, []))) := by
  induction nodes generalizing issued with
  | nil => simp [collectTargets, sampleHiddenInputs, hiddenImages, simulateQ_pure]
  | cons n ns ih =>
    have hlen : issued.length < (preProblem P I f).numTargets := by
      change issued.length < targetCapacity f I
      simp only [List.length_cons] at hcap
      omega
    have htfresh : TweakFresh Prod.fst issued [] (tweak P n) := by
      simpa [TweakFresh, TweakReserved, List.mem_map] using hfresh n (by simp)
    simp only [collectTargets, simulateQ_bind, StateT.run_bind]
    rw [collect_query_pre, SM_DT_PRE_challengeOracle_run_of_fresh hlen htfresh]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    simp only [sampleHiddenInputs, bind_assoc]
    apply bind_congr
    intro input
    have htail : ∀ m ∈ ns, tweak P m ∉ (issued ++ [(tweak P n, input)]).map Prod.fst := by
      intro m hm
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton, not_or]
      refine ⟨hfresh m (by simp [hm]), ?_⟩
      intro heq
      have hmn := tweak_injective P f I heq
      exact (List.nodup_cons.mp hnd).1 (hmn ▸ hm)
    have htailcap : (issued ++ [(tweak P n, input)]).length + ns.length ≤
        targetCapacity f I := by
      simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at hcap
      omega
    simp only [simulateQ_bind, StateT.run_bind]
    rw [ih (issued ++ [(tweak P n, input)]) (List.nodup_cons.mp hnd).2 htail htailcap]
    simp [hiddenImages, monad_norm, List.append_assoc, preProblem, SM_DT_PRE_Problem.standalone]

/-- Empty-history PRE setup accepts exactly the fixed target list, preserving hidden inputs. -/
private theorem collectTargets_run_pre_empty [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family) (pp : PP) :
    (simulateQ (preOracle P I f pp)
      (collectTargets P f I (targetList f I))).run ([], []) =
      (do
        let hidden ← sampleHiddenInputs P I f (targetList f I)
        pure (some (hiddenImages P f pp hidden), (hidden, []))) := by
  simpa using collectTargets_run_pre P I f pp (targetList f I) []
    (targetList_nodup f I) (by simp) (by simp)

/-- PRE's hidden transcript has exactly the registered tweaks in the registered order. -/
private theorem sampleHiddenInputs_tweaks [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (nodes : List (Target f I)) (hidden : List (T × Input f H v))
    (hh : hidden ∈ support (sampleHiddenInputs P I f nodes)) :
    hidden.map Prod.fst = nodes.map (tweak P) := by
  induction nodes generalizing hidden with
  | nil => simpa [sampleHiddenInputs] using hh
  | cons n ns ih =>
    simp only [sampleHiddenInputs, mem_support_bind_iff] at hh
    obtain ⟨input, _, rest, hrest, hreturn⟩ := hh
    have heq : hidden = (tweak P n, input) :: rest := by simpa using hreturn
    subst hidden
    simpa using congrArg (tweak P n :: ·) (ih rest hrest)

/-- Real UD responses are exactly the images of the independent hidden PRE input transcript. -/
private theorem sampleResponses_real_eq_hiddenImages [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (pp : PP) (nodes : List (Target f I)) :
    sampleResponses P I f .real pp nodes =
      hiddenImages P f pp <$> sampleHiddenInputs P I f nodes := by
  induction nodes with
  | nil => simp [sampleResponses, sampleHiddenInputs, hiddenImages]
  | cons n ns ih =>
    simp [sampleResponses, sampleHiddenInputs, hiddenImages, SM_DT_UD_response,
      udProblem, SM_DT_UD_Problem.standalone, ih, monad_norm]

/-- Ideal challenge responses are independent canonical digest draws in registration order. -/
private theorem sampleResponses_ideal_eq_replicate [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (pp : PP) (nodes : List (Target f I)) :
    sampleResponses P I f .ideal pp nodes = OracleComp.replicate nodes.length ($ᵗ H) := by
  induction nodes with
  | nil => simp [sampleResponses, OracleComp.replicate_zero]
  | cons n ns ih =>
    simp [sampleResponses, SM_DT_UD_response, udProblem, SM_DT_UD_Problem.standalone,
      OracleComp.replicate_succ_bind, ih]

/-- Reindexing all ordered samples by accepted target positions preserves every continuation. -/
private theorem orderedTable_bind_eq_table [SampleableType H] {S : Type} [MeasurableSpace S]
    (f : Family) (I : Interval h) (next : (Target f I → H) → ProbComp S) :
    𝒟[(do
      let answers ← Fin.mOfFn (targetCapacity f I) (fun _ => ($ᵗ H : ProbComp H))
      next (fun n => answers (targetEquiv f I n)))] =
      𝒟[sampleTable f I >>= next] := by
  let : MeasurableSpace H := ⊤
  let e := Equiv.arrowCongr (targetEquiv f I).symm (Equiv.refl H)
  have he : Function.Bijective e := e.bijective
  exact evalDist_bind_bijective_uniform_cross
    (Fin.mOfFn (targetCapacity f I) (fun _ => ($ᵗ H : ProbComp H)))
    (sampleTable f I) (orderedTable_uniform (targetCapacity f I)) (sampleTable_uniform f I)
    e he next

/-- Complete answers in issue order, together with the independently sampled other family. -/
private structure Setup (f : Family) (I : Interval h) (H : Type) where
  /-- Digest returned at each accepted target position. -/
  answers : Fin (targetCapacity f I) → H
  /-- Only the other family is privately sampled by the reduction. -/
  others : Target f.other I → H

/-- The retained family table uses the proved registration position. -/
private def Setup.selected {f : Family} {I : Interval h} (st : Setup f I H) : Target f I → H :=
  fun n => st.answers ⟨targetIndex n, targetIndex_lt n⟩

/-- The complete cached table passed to all adaptive signing computation. -/
private def Setup.fillers {f : Family} {I : Interval h} (st : Setup f I H) : Fillers I H :=
  assemble f I st.selected st.others

/-- Complete setup from responses in issue order; an incorrect length remains explicit failure. -/
private noncomputable def completeSetup [SampleableType H] (f : Family) (I : Interval h)
    (answers : List H) : ProbComp (Option (Setup f I H)) :=
  if hc : answers.length = targetCapacity f I then do
    let others ← sampleTable f.other I
    pure (some ⟨fun j => answers[j.val]'(by omega), others⟩)
  else pure none

/-- A full ordered response function passes the length check and is retained without alteration. -/
private theorem completeSetup_ofFn [SampleableType H] (f : Family) (I : Interval h)
    (answers : Fin (targetCapacity f I) → H) :
    completeSetup f I (List.ofFn answers) = (do
      let others ← sampleTable f.other I
      pure (some (⟨answers, others⟩ : Setup f I H))) := by
  simp only [completeSetup, List.length_ofFn]
  apply bind_congr
  intro others
  congr 3
  funext j
  simp

/-- Successful setup preserves the exact digest at each accepted registration index. -/
private theorem completeSetup_lookup [SampleableType H] (f : Family) (I : Interval h)
    (answers : List H) (st : Setup f I H)
    (hs : some st ∈ support (completeSetup f I answers)) (n : Target f I) :
    answers[targetIndex n]? = some (st.fillers n.val) := by
  unfold completeSetup at hs
  split at hs
  · rename_i hc
    simp only [mem_support_bind_iff] at hs
    obtain ⟨others, _, hreturn⟩ := hs
    have heq : st = ⟨fun j => answers[j.val]'(by omega), others⟩ := by
      simpa using hreturn
    subst st
    have hi : targetIndex n < answers.length := by rw [hc]; exact targetIndex_lt n
    simp [Setup.fillers, Setup.selected, List.getElem?_eq_getElem hi]
  · simp at hs

/-- Exact-length responses cannot turn into a setup failure. -/
private theorem completeSetup_ne_none [SampleableType H] (f : Family) (I : Interval h)
    (answers : List H) (hc : answers.length = targetCapacity f I)
    (st : Option (Setup f I H)) (hs : st ∈ support (completeSetup f I answers)) :
    st ≠ none := by
  simp only [completeSetup, dite_eq_left hc, mem_support_bind_iff] at hs
  obtain ⟨others, _, hreturn⟩ := hs
  have heq : st = some ⟨fun j => answers[j.val]'(by omega), others⟩ := by
    simpa using hreturn
  simp [heq]

/-- Register every selected coordinate before privately sampling the other family. -/
private noncomputable def setup [SampleableType H]
    (P : HashInstance PP T X H h w v) (f : Family) (I : Interval h) :
    OracleComp
      (unifSpec + (SM_DT_UD_challengeSpec T H + collectionSpec (.empty PP T H)))
      (Option (Setup f I H)) := do
  let responses ← collectTargets P f I (targetList f I)
  match responses with
  | none => pure none
  | some answers => liftComp (completeSetup f I answers) _

private theorem udOracle_liftComp [SampleableType H] [DecidableEq T] {S : Type}
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (world : SM_DT_UD_World) (pp : PP) (oa : ProbComp S) (state : SM_DT_UD_State T) :
    (simulateQ (udOracle P I f world pp) (liftComp oa _)).run state =
      (fun x => (x, state)) <$> oa := by
  dsimp only [udOracle, udProblem, SM_DT_UD_Problem.standalone]
  rw [SM_DT_UD_oracles, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp

private theorem preOracle_liftComp [SampleableType H] [DecidableEq T] {S : Type}
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (pp : PP) (oa : ProbComp S) (state : SM_DT_PRE_State T (Input f H v)) :
    (simulateQ (preOracle P I f pp) (liftComp oa _)).run state =
      (fun x => (x, state)) <$> oa := by
  dsimp only [preOracle, preProblem, SM_DT_PRE_Problem.standalone]
  rw [SM_DT_PRE_oracles, QueryImpl.simulateQ_add_liftComp_left,
    simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp

/-- Entire joint UD setup law: retained private state and accepted challenge history. -/
private theorem setup_run_ud [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (world : SM_DT_UD_World) (pp : PP) :
    (simulateQ (udOracle P I f world pp) (setup P f I)).run ([], []) =
      (do
        let answers ← sampleResponses P I f world pp (targetList f I)
        let st ← completeSetup f I answers
        pure (st, ((targetList f I).map (tweak P), []))) := by
  simp only [setup, simulateQ_bind, StateT.run_bind, collectTargets_run_ud_empty,
    bind_assoc, pure_bind]
  simp only [udOracle_liftComp, map_eq_bind_pure_comp, Function.comp_def]

/-- Entire joint PRE setup law, including the hidden inputs withheld from the adversary. -/
private theorem setup_run_pre [SampleableType H] [DecidableEq T]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family) (pp : PP) :
    (simulateQ (preOracle P I f pp) (setup P f I)).run ([], []) =
      (do
        let hidden ← sampleHiddenInputs P I f (targetList f I)
        let st ← completeSetup f I (hiddenImages P f pp hidden)
        pure (st, (hidden, []))) := by
  simp only [setup, simulateQ_bind, StateT.run_bind, collectTargets_run_pre_empty,
    bind_assoc, pure_bind]
  simp only [preOracle_liftComp, map_eq_bind_pure_comp, Function.comp_def]

/-- The actual UD adversary: pre-seed registration, retained-table view, then the opening event. -/
noncomputable def udAdversary
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) : SM_DT_UD_Adversary (udProblem P I f) where
  State := Option (Setup f I H)
  pick := setup P f I
  distinguish state pp := match state with
    | none => pure false
    | some st => do
      let out ← view P enc K I A pp st.fillers
      pure (openingEvent P enc K I f pp st.fillers out)

/-- The actual PRE adversary returns the accepted target and the extracted original input.
Failure emits the out-of-range capacity sentinel and a properly sampled family input. -/
noncomputable def preAdversary
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) : SM_DT_PRE_Adversary (preProblem P I f) where
  State := Option (Setup f I H)
  choose := setup P f I
  invert state pp := do
    let result ← match state with
      | none => pure none
      | some st => do
        let out ← view P enc K I A pp st.fillers
        pure (extractFillerOpening P enc K I f pp st.fillers out)
    match result with
    | some (n, input) => pure (targetIndex n, input)
    | none => do
      let input ← $ᵗ Input f H v
      pure (targetCapacity f I, input)

/-- Every accepted target position names its original tweak in the hidden PRE transcript. -/
private theorem hidden_target_lookup [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (hidden : List (T × Input f H v))
    (hh : hidden ∈ support (sampleHiddenInputs P I f (targetList f I))) (n : Target f I) :
    ∃ sampled, hidden[targetIndex n]? = some (tweak P n, sampled) := by
  have ht := sampleHiddenInputs_tweaks P I f (targetList f I) hidden hh
  have hi : targetIndex n < (targetList f I).length := by simpa using targetIndex_lt n
  have hl : (hidden[targetIndex n]?).map Prod.fst = some (tweak P n) := by
    rw [← List.getElem?_map, ht, List.getElem?_map, List.getElem?_eq_getElem hi,
      targetList_getElem_targetIndex]
    rfl
  cases hx : hidden[targetIndex n]? with
  | none => simp [hx] at hl
  | some entry =>
    obtain ⟨t, sampled⟩ := entry
    simp only [hx, Option.map_some, Option.some.injEq] at hl
    subst t
    exact ⟨sampled, rfl⟩

/-- The retained response at an accepted target is the image of that target's hidden PRE input. -/
private theorem completeSetup_target_image [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family) (pp : PP)
    (hidden : List (T × Input f H v))
    (hh : hidden ∈ support (sampleHiddenInputs P I f (targetList f I)))
    (st : Setup f I H)
    (hs : some st ∈ support (completeSetup f I (hiddenImages P f pp hidden)))
    (n : Target f I) :
    ∃ sampled, hidden[targetIndex n]? = some (tweak P n, sampled) ∧
      TweakableHash.eval P.thf pp (tweak P n) (embed P f sampled) = st.fillers n.val := by
  obtain ⟨sampled, hx⟩ := hidden_target_lookup P I f hidden hh n
  refine ⟨sampled, hx, ?_⟩
  have hi := completeSetup_lookup f I (hiddenImages P f pp hidden) st hs n
  simpa only [hiddenImages, List.getElem?_map, hx, Option.map_some, Option.some.injEq] using hi

/-- The fallback index is outside the full accepted PRE transcript. -/
private theorem hidden_sentinel_lookup [SampleableType H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (f : Family)
    (hidden : List (T × Input f H v))
    (hh : hidden ∈ support (sampleHiddenInputs P I f (targetList f I))) :
    hidden[targetCapacity f I]? = none := by
  have ht := congrArg List.length (sampleHiddenInputs_tweaks P I f (targetList f I) hidden hh)
  have hl : hidden.length = targetCapacity f I := by simpa using ht
  simp [← hl]

/-- Explicit product-response hybrid followed by the actual retained-table UD continuation. -/
private noncomputable def hybrid
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (world : SM_DT_UD_World) : ProbComp Bool := do
  let pp ← TweakableHash.seedGen P.thf
  let answers ← sampleResponses P I f world pp (targetList f I)
  let st ← completeSetup f I answers
  (udAdversary P enc K I A f).distinguish st pp

/-- Both entire Boolean UD output laws agree with the explicit product-response hybrids. -/
private theorem udExperiment_eq_hybrid
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (udAdversary P enc K I A f) = hybrid P enc K I A f world := by
  change (do
    let pp ← TweakableHash.seedGen P.thf
    let (st, _, _) ← (simulateQ (udOracle P I f world pp) (setup P f I)).run ([], [])
    (udAdversary P enc K I A f).distinguish st pp) = _
  simp only [setup_run_ud, bind_assoc, pure_bind, hybrid]

/-- The authoritative PRE winning check on a retained hidden transcript. -/
private def preCheck [DecidableEq H] (P : HashInstance PP T X H h w v)
    (f : Family) (pp : PP) (hidden : List (T × Input f H v)) (guess : ℕ × Input f H v) : Bool :=
  let (j, input) := guess
  match hidden[j]? with
  | none => false
  | some (t, sampled) => decide (TweakableHash.eval P.thf pp t (embed P f input) =
      TweakableHash.eval P.thf pp t (embed P f sampled))

/-- The ideal hybrid has the joint law of both independently sampled complete family tables. -/
private theorem hybrid_ideal_measure_eq_tables
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    𝒟[hybrid P enc K I A f .ideal] = 𝒟[(do
      let pp ← TweakableHash.seedGen P.thf
      let selected ← sampleTable f I
      let other ← sampleTable f.other I
      let fillers := assemble f I selected other
      let out ← view P enc K I A pp fillers
      pure (openingEvent P enc K I f pp fillers out))] := by
  unfold hybrid
  simp only [sampleResponses_ideal_eq_replicate, length_targetList, replicate_eq_ofFn_mOfFn,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, completeSetup_ofFn,
    udAdversary, Setup.fillers]
  apply evalDist_bind_congr_of_support
  intro pp _
  exact orderedTable_bind_eq_table f I (fun selected => do
    let other ← sampleTable f.other I
    let fillers := assemble f I selected other
    let out ← view P enc K I A pp fillers
    pure (openingEvent P enc K I f pp fillers out))

/-- Explicit PRE experiment retaining the full hidden-input transcript until its winning check. -/
private noncomputable def preExplicit
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) : ProbComp Bool := do
  let pp ← TweakableHash.seedGen P.thf
  let hidden ← sampleHiddenInputs P I f (targetList f I)
  let st ← completeSetup f I (hiddenImages P f pp hidden)
  let guess ← (preAdversary P enc K I A f).invert st pp
  pure (preCheck P f pp hidden guess)

/-- The authoritative PRE experiment has exactly the explicit joint hidden-transcript law. -/
private theorem preExperiment_eq_explicit
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    SM_DT_PRE_Experiment (preAdversary P enc K I A f) = preExplicit P enc K I A f := by
  have hrun (pp : PP) :
      (simulateQ (SM_DT_PRE_oracles (preProblem P I f) pp)
        (preAdversary P enc K I A f).choose).run ([], []) =
        (do
          let hidden ← sampleHiddenInputs P I f (targetList f I)
          let st ← completeSetup f I (hiddenImages P f pp hidden)
          pure (st, (hidden, []))) := setup_run_pre P I f pp
  unfold SM_DT_PRE_Experiment preExplicit
  simp only [hrun, bind_assoc, pure_bind]
  simp only [preProblem, SM_DT_PRE_Problem.standalone]
  apply bind_congr
  intro pp
  apply bind_congr
  intro hidden
  apply bind_congr
  intro st
  apply bind_congr
  intro guess
  obtain ⟨j, input⟩ := guess
  cases hx : hidden[j]? with
  | none => simp [preCheck, hx]
  | some entry => cases entry; simp [preCheck, hx]; rfl


/-- On a valid retained PRE setup, actual inversion has the entire opening-observation law.
The none branch loses via the sentinel; its proper input sample is lossless in native ProbComp. -/
private theorem preContinuation_measure_eq_observation
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (pp : PP)
    (hidden : List (T × Input f H v))
    (hh : hidden ∈ support (sampleHiddenInputs P I f (targetList f I)))
    (st : Setup f I H)
    (hs : some st ∈ support (completeSetup f I (hiddenImages P f pp hidden))) :
    𝒟[(preAdversary P enc K I A f).invert (some st) pp >>=
      fun guess => pure (preCheck P f pp hidden guess)] =
      𝒟[(udAdversary P enc K I A f).distinguish (some st) pp] := by
  simp only [preAdversary, udAdversary, pure_bind, bind_assoc]
  apply evalDist_bind_congr_of_support
  intro out _
  cases hx : extractFillerOpening P enc K I f pp st.fillers out with
  | none =>
    simp only [preCheck, openingEvent, hx, Option.isSome_none]
    simp only [bind_assoc, pure_bind, hidden_sentinel_lookup P I f hidden hh]
    exact OracleComp.evalDist_bind_const ($ᵗ Input f H v) (pure false)
  | some result =>
    obtain ⟨n, input⟩ := result
    obtain ⟨sampled, hi, himage⟩ := completeSetup_target_image P I f pp hidden hh st hs n
    have hpre := extractFillerOpening_sound P enc K I f pp st.fillers out n input hx
    have hhash : TweakableHash.eval P.thf pp (tweak P n) (embed P f input) =
        TweakableHash.eval P.thf pp (tweak P n) (embed P f sampled) := hpre.trans himage.symm
    simp [hx, preCheck, hi, hhash, openingEvent]


/-- The real product-response hybrid and the actual PRE adversary have identical Boolean laws. -/
private theorem hybrid_real_measure_eq_preExperiment
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    ProbCompRuntime.probComp.evalDist (hybrid P enc K I A f .real) =
      ProbCompRuntime.probComp.evalDist (SM_DT_PRE_Experiment (preAdversary P enc K I A f)) := by
  simp only [ProbCompRuntime.probComp_evalDist, preExperiment_eq_explicit]
  unfold hybrid preExplicit
  simp only [sampleResponses_real_eq_hiddenImages, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind]
  apply evalDist_bind_congr_of_support
  intro pp _
  apply evalDist_bind_congr_of_support
  intro hidden hh
  apply evalDist_bind_congr_of_support
  intro st hs
  cases st with
  | none =>
    have ht := congrArg List.length (sampleHiddenInputs_tweaks P I f (targetList f I) hidden hh)
    have hl : (hiddenImages P f pp hidden).length = targetCapacity f I := by
      simpa [hiddenImages] using ht
    exact (completeSetup_ne_none f I _ hl none hs rfl).elim
  | some st =>
    exact (preContinuation_measure_eq_observation P enc K I A f pp hidden hh st hs).symm


/-- Each family's ideal product-response opening event has one actual UD and one actual PRE term.
This inequality concerns only the extracted filler-opening event. -/
private theorem hybrid_ideal_le_advantages
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    ProbCompRuntime.probComp.evalDist (hybrid P enc K I A f .ideal) {true} ≤
      SM_DT_UD_Advantage (udAdversary P enc K I A f) +
        SM_DT_PRE_Advantage (preAdversary P enc K I A f) := by
  simp only [ProbCompRuntime.probComp_evalDist]
  have hreal : 𝒟[hybrid P enc K I A f .real] =
      𝒟[SM_DT_PRE_Experiment (preAdversary P enc K I A f)] := by
    simpa only [ProbCompRuntime.probComp_evalDist] using
      hybrid_real_measure_eq_preExperiment P enc K I A f
  have hmass : 𝒟[hybrid P enc K I A f .real] {true} =
      SM_DT_PRE_Advantage (preAdversary P enc K I A f) := by
    rw [hreal]
    rfl
  have hdist : (𝒟[hybrid P enc K I A f .ideal]).boolDist
      𝒟[hybrid P enc K I A f .real] =
      SM_DT_UD_Advantage (udAdversary P enc K I A f) := by
    rw [MeasureTheory.Measure.boolDist_comm,
      ← udExperiment_eq_hybrid P enc K I A f .real,
      ← udExperiment_eq_hybrid P enc K I A f .ideal]
    rfl
  simpa only [hmass, hdist, add_comm] using
    MeasureTheory.Measure.apply_true_le_add_boolDist
      𝒟[hybrid P enc K I A f .ideal] 𝒟[hybrid P enc K I A f .real]


/-- The ideal hybrid and actual ideal source have the same entire Boolean opening measure. -/
private theorem hybrid_ideal_measure_eq_sourceOpening
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    ProbCompRuntime.probComp.evalDist (hybrid P enc K I A f .ideal) =
      ProbCompRuntime.probComp.evalDist (sourceOpening P enc K I A f) := by
  rw [sourceOpening_measure_eq_fillers_view]
  simp only [ProbCompRuntime.probComp_evalDist, hybrid_ideal_measure_eq_tables]
  apply evalDist_bind_congr_of_support
  intro pp _
  let : MeasurableSpace H := ⊤
  let next (fillers : Fillers I H) : ProbComp Bool := do
    let out ← view P enc K I A pp fillers
    pure (openingEvent P enc K I f pp fillers out)
  have htables : 𝒟[(do
      let selected ← (sampleTable f I : ProbComp (Target f I → H))
      let other ← sampleTable f.other I
      pure (assemble f I selected other)) >>= next] = 𝒟[sampleFillers I H >>= next] := by
    rw [evalDist_bind_of_discrete, assemble_tables_measure, ← evalDist_bind_of_discrete]
  simpa only [bind_assoc, pure_bind] using htables

/-- An ideal source filler opening is bounded by the actual original-hash UD and PRE adversaries,
with coefficient one and the exact selected-family multi-target capacity. -/
theorem sourceOpening_le_advantages
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    ProbCompRuntime.probComp.evalDist (sourceOpening P enc K I A f) {true} ≤
      SM_DT_UD_Advantage (udAdversary P enc K I A f) +
        SM_DT_PRE_Advantage (preAdversary P enc K I A f) := by
  rw [← hybrid_ideal_measure_eq_sourceOpening]
  exact hybrid_ideal_le_advantages P enc K I A f


/-- Full-range registration makes no challenge query, for either family. -/
private theorem collectTargets_full (P : HashInstance PP T X H h w v) (f : Family) :
    collectTargets P f (Interval.full h) (targetList f (Interval.full h)) = pure (some []) := by
  simp [collectTargets]

private theorem native_bind_false {S : Type} (draw : ProbComp S) (next : S → ProbComp Bool)
    (hn : ∀ x, 𝒟[next x] = 𝒟[(pure false : ProbComp Bool)]) :
    𝒟[draw >>= next] = 𝒟[(pure false : ProbComp Bool)] :=
  (evalDist_bind_congr draw next (fun _ => pure false) hn).trans
    (OracleComp.evalDist_bind_const draw (pure false))

/-- Both full-range hybrid worlds have exactly the returned-false Boolean measure. -/
private theorem hybrid_full_measure
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (world : SM_DT_UD_World) :
    𝒟[hybrid P enc K (Interval.full h) A f world] = 𝒟[(pure false : ProbComp Bool)] := by
  have hcont (pp : PP) (st : Option (Setup f (Interval.full h) H)) :
      𝒟[(udAdversary P enc K (Interval.full h) A f).distinguish st pp] =
        𝒟[(pure false : ProbComp Bool)] := by
    cases st with
    | none => rfl
    | some st => simp [udAdversary, openingEvent_full]
  calc
    _ = 𝒟[(do
      let pp ← TweakableHash.seedGen P.thf
      let answers ← sampleResponses P (Interval.full h) f world pp (targetList f (Interval.full h))
      let _ ← completeSetup f (Interval.full h) answers
      pure false : ProbComp Bool)] := by
        unfold hybrid
        apply evalDist_bind_congr_of_support
        intro pp _
        apply evalDist_bind_congr_of_support
        intro answers _
        apply evalDist_bind_congr_of_support
        intro st _
        exact hcont pp st
    _ = _ := by
      apply native_bind_false
      intro pp
      apply native_bind_false
      intro answers
      exact OracleComp.evalDist_bind_const _ _

/-- The actual full-range UD experiments both return false with total mass one. -/
theorem udExperiment_full_measure
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) (world : SM_DT_UD_World) :
    𝒟[SM_DT_UD_Experiment world (udAdversary P enc K (Interval.full h) A f)] =
      𝒟[(pure false : ProbComp Bool)] := by
  rw [udExperiment_eq_hybrid, hybrid_full_measure]

/-- The actual full-range PRE experiment returns false with total mass one. -/
theorem preExperiment_full_measure
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    𝒟[SM_DT_PRE_Experiment (preAdversary P enc K (Interval.full h) A f)] =
      𝒟[(pure false : ProbComp Bool)] := by
  have heq := hybrid_real_measure_eq_preExperiment P enc K (Interval.full h) A f
  simp only [ProbCompRuntime.probComp_evalDist] at heq
  rw [← heq, hybrid_full_measure]

/-- Full-range actual UD advantage is zero for each empty target family. -/
@[simp] theorem udAdvantage_full
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    SM_DT_UD_Advantage (udAdversary P enc K (Interval.full h) A f) = 0 := by
  simp [SM_DT_UD_Advantage, udExperiment_full_measure]

/-- Full-range actual PRE advantage is zero for each empty target family. -/
@[simp] theorem preAdvantage_full
    [SampleableType H] [SampleableType R] [DecidableEq T] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) (f : Family) :
    SM_DT_PRE_Advantage (preAdversary P enc K (Interval.full h) A f) = 0 := by
  simp [SM_DT_PRE_Advantage, preExperiment_full_measure]

end GXMSS.Interval.Filler
