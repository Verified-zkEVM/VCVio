/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Auxiliary.FillerOpening
public import HashSig.GXMSS.Security.Interval.Auxiliary.FillerTargets
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
import all HashSig.GXMSS.Security.Interval.Auxiliary.FillerTargets

/-!
# Seed-independent filler target setup

The actual challenge collectors retain accepted issue order and abort on refusal. Explicit
UD/PRE collector laws preserve both private setup and the entire original target histories.
-/

public section

namespace GXMSS.Interval.Filler

open GXMSS.IntervalMerkle GXMSS.Interval.MerkleWitnesses GXMSS.Interval
open SyncSignatureUnforgeability OracleSpec OracleComp TweakableHash IncomparableEncoding

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
  | nil => simp [collectTargets, sampleResponses]
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
  | nil => simp [collectTargets, sampleHiddenInputs, hiddenImages]
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

end GXMSS.Interval.Filler
