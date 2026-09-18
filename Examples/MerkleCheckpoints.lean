/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.MerkleTree.MultiExtractability.DelayedObservation
import VCVio.EvalDist.Monad.UniformTable

/-!
# Merkle checkpoint and cache-reset counterexamples

A concrete execution of the multi-extractability game has frozen-checkpoint failure
probability one half, while a terminal-log observer reports zero. The extraction-drift
term is exactly one half. Honest construction and batch verification also demonstrate
why fresh random responses across phases differ from one retained random function:
shared-cache acceptance is one, whereas resampling gives one half.
-/

public section

open OracleComp OracleSpec MeasureTheory ProbabilityTheory
open BinaryTree InductiveMerkleTree MerkleTreeMultiExtractability
open MerkleTreeMultiExtractability.DelayedObservation

namespace MerkleCheckpoints


/-- A Merkle compression query contains two child labels. -/
abbrev Query := Bool × Bool

/-- Each fresh oracle address receives a uniform Boolean response. -/
noncomputable local instance nativeUniform : IsUniformMeasureSpec (Query →ₒ Bool) :=
  IsUniformMeasureSpec.ofFintypeInhabited (Query →ₒ Bool)

/-- Addressed binary-node query interface with one address. -/
@[expose]
def model : MerkleTreeExtractability.NodeQueryModel Query Unit Bool where
  view := { address := fun _ => (), input := id }
  mkQuery _ input := input
  address_mkQuery := by intros; rfl
  input_mkQuery := by intros; rfl

/-- One internal node with two leaves. -/
@[expose]
def skeleton : Skeleton := .internal .leaf .leaf

/-- The single public configuration of the checkpoint experiment. -/
@[expose]
def config : Configuration Unit Unit where
  skeleton _ := skeleton
  addressKey _ _ := ()

/-- A batch opening revealing both false-valued leaves. -/
@[expose]
def opening : BatchOpening Bool skeleton where
  selector := .internal (.leaf true) (.leaf true)
  values := (false, false)
  proof := .internalBoth .leaf .leaf

/-- A commitment emitted before any oracle query is recorded. -/
@[expose]
def checkpoint : Checkpoint Query Bool config () := ⟨false, []⟩

/-- The state containing the one frozen checkpoint. -/
@[expose]
def extractorState : ExtractorState Unit Query Unit Bool config :=
  { cumulativeLog := [], checkpoints := [⟨(), checkpoint⟩] }

/-- The opening claim against the recorded commitment. -/
@[expose]
def claim : OpeningClaim Query Bool config := ⟨(), checkpoint, opening⟩

/-- Commit before querying, then learn the opening during the terminal phase. -/
abbrev adversary : Adversary Unit Query Unit Bool config where
  committer := {
    State := Unit
    initialState := ()
    commit _ _ := pure ((), false, ()) }
  opening _ _ := do
    let _ ← (query (spec := Query →ₒ Bool) (false, false) : OracleComp (Query →ₒ Bool) Bool)
    pure [claim]

/-- The terminal transcript produced for each sampled oracle response. -/
@[expose]
def outcome (reply : Bool) : Transcript Unit Query Unit Bool config :=
  { extractorState
    attempts := [⟨(), { checkpoint, opening, accepted := reply == false }⟩]
    terminalSuffix := [⟨(false, false), reply⟩] }

theorem verifier_eq (root : Bool) :
    MerkleTreeBatchExtractability.verifyOpening model (config.addressKey ()) root opening =
      (query (spec := Query →ₒ Bool) (false, false) >>= fun reply => pure (reply == root)) := by
  rfl

theorem game_eq : extractabilityGame model config 1 adversary =
    (query (spec := Query →ₒ Bool) (false, false) >>= fun reply => pure (outcome reply)) := by
  simp [extractabilityGame, extractabilityInner, SequentialCommitter.runFromEmpty,
    SequentialCommitter.runCommitments, adversary, ExtractorState.empty,
    ExtractorState.record, verifyOpeningClaims, claim, verifier_eq,
    OracleSpec.withCacheOverlay, OracleComp.withQueryLog, outcome, extractorState, checkpoint]

theorem frozenTree_eq : checkpoint.extractedTree model.view =
    .internal (some false) (.leaf none) (.leaf none) := rfl

theorem terminalTree_false : (atTerminal (outcome false) checkpoint).extractedTree model.view =
    .internal (some false) (.leaf (some false)) (.leaf (some false)) := rfl

theorem terminalOpening_false :
    (atTerminal (outcome false) checkpoint).extractedOpening model.view opening =
      opening.map some := rfl

theorem frozenOpening_ne : checkpoint.extractedOpening model.view opening ≠ opening.map some := by
  intro h
  cases h

theorem openingFailure_outcome (reply : Bool) :
    HasAcceptedOpeningDisagreement model.view (outcome reply).extractorState
      (outcome reply).attempts ↔ reply = false := by
  cases reply with
  | false =>
      refine ⟨fun _ => rfl, fun _ => ?_⟩
      exact ⟨(), { checkpoint, opening, accepted := true }, by simp [outcome],
        by simp [outcome, extractorState], rfl, frozenOpening_ne⟩
  | true =>
      simp [HasAcceptedOpeningDisagreement, AcceptedOpeningDisagreement, outcome, extractorState]

theorem no_equalRootFailure_outcome (reply : Bool) :
    ¬ HasEqualRootExtractionDisagreement model.view (outcome reply).extractorState := by
  simp [HasEqualRootExtractionDisagreement, outcome, extractorState]

theorem publicFailure_outcome (reply : Bool) :
    (outcome reply).HasOpeningOrEqualRootDisagreement model ↔ reply = false := by
  rw [Transcript.HasOpeningOrEqualRootDisagreement, OpeningOrEqualRootDisagreement,
    or_iff_left (no_equalRootFailure_outcome reply)]
  exact openingFailure_outcome reply

theorem no_lateFailure_outcome (reply : Bool) :
    ¬ LateOpeningFailure model.view (outcome reply) := by
  cases reply with
  | false =>
      simpa [LateOpeningFailure, AcceptedOpeningDisagreement, outcome, extractorState,
        atTerminal] using (fun tag : Unit => by
          cases tag
          exact terminalOpening_false)
  | true =>
      simp [LateOpeningFailure, AcceptedOpeningDisagreement, outcome, extractorState, atTerminal]

theorem drift_outcome_false : Drift model.view (outcome false) := by
  refine ⟨(), checkpoint, by simp [outcome, extractorState], ?_⟩
  change checkpoint.extractedTree model.view ≠
    (atTerminal (outcome false) checkpoint).extractedTree model.view
  rw [frozenTree_eq, terminalTree_false]
  intro h
  cases h

theorem no_drift_outcome_true : ¬ Drift model.view (outcome true) := by
  simp only [Drift, HasCheckpointTerminalExtractionDisagreement, outcome, extractorState,
    CheckpointTerminalExtractionDisagreement]
  rintro ⟨tag, checkpoint, hmem, hne⟩
  cases tag
  simp only [List.mem_singleton] at hmem
  cases hmem
  exact hne rfl

/-- The actual library constructor computes the honest root from two raw leaves. -/
@[expose]
def honestRoot : OracleComp (Query →ₒ Bool) Bool :=
  FullData.getRootValue <$> (buildMerkleTree
    (.internal (.leaf false) (.leaf false) : LeafData Bool skeleton))

theorem honestRoot_eq : honestRoot =
    (query (spec := Query →ₒ Bool) (false, false) : OracleComp (Query →ₒ Bool) Bool) := by
  simp [honestRoot]
  rfl

/-- Honest construction and the existing batch verifier, sharing one live cache. -/
@[expose]
def honestShared : OracleComp (Query →ₒ Bool) Bool :=
  (Query →ₒ Bool).withCacheOverlay ∅ do
    let root ← honestRoot
    MerkleTreeBatchExtractability.verifyOpening model (config.addressKey ()) root opening

/-- The same honest computation with a fresh cache for verification. -/
@[expose]
def honestReset : OracleComp (Query →ₒ Bool) Bool := do
  let root ← (Query →ₒ Bool).withCacheOverlay ∅ honestRoot
  (Query →ₒ Bool).withCacheOverlay ∅
    (MerkleTreeBatchExtractability.verifyOpening model (config.addressKey ()) root opening)

theorem honestShared_eq : honestShared =
    (query (spec := Query →ₒ Bool) (false, false) >>= fun _ => pure true) := by
  simp [honestShared, honestRoot_eq, verifier_eq, withCacheOverlay]

theorem honestReset_eq : honestReset =
    (query (spec := Query →ₒ Bool) (false, false) >>= fun root =>
      query (spec := Query →ₒ Bool) (false, false) >>= fun reply => pure (reply == root)) := by
  simp [honestReset, honestRoot_eq, verifier_eq, withCacheOverlay]

/-- Clearing a memo cache is harmless here if both phases still read one fixed
underlying hash function. The invalid change is to resample its answers. -/
theorem reset_same_table_accepts (table : Query → Bool) :
    evalWithAnswerFn (QueryImpl.ofFn table) honestReset = true := by
  rw [honestReset_eq]
  change (table (false, false) == table (false, false)) = true
  simp

/-- The concrete transcript model uses the discrete measurable structure. -/
local instance transcriptMeasurable : MeasurableSpace (Transcript Unit Query Unit Bool config) := ⊤
local instance transcriptDiscrete :
    DiscreteMeasurableSpace (Transcript Unit Query Unit Bool config) :=
  ⟨fun _ => trivial⟩

theorem game_law : 𝒟[extractabilityGame model config 1 adversary] =
    (uniformOn (Set.univ : Set Bool)).map outcome := by
  rw [game_eq, bind_pure_comp, evalDist_map_of_discrete, evalDist_query_uniform]

theorem publicFailure_probability :
    𝒟[extractabilityGame model config 1 adversary]
      {tr | tr.HasOpeningOrEqualRootDisagreement model} = (1 : ENNReal) / 2 := by
  rw [game_law, Measure.map_apply (measurable_of_countable _) (by trivial)]
  have hevent : outcome ⁻¹' {tr | tr.HasOpeningOrEqualRootDisagreement model} = {false} := by
    ext reply
    exact publicFailure_outcome reply
  rw [hevent, uniformOn_univ_apply_singleton]
  simp

theorem lateFailure_probability :
    𝒟[extractabilityGame model config 1 adversary]
      {tr | LateOpeningFailure model.view tr} = 0 := by
  rw [game_law, Measure.map_apply (measurable_of_countable _) (by trivial)]
  have hevent : outcome ⁻¹' {tr | LateOpeningFailure model.view tr} = ∅ := by
    ext reply
    exact iff_false_intro (no_lateFailure_outcome reply)
  rw [hevent, measure_empty]

theorem drift_probability :
    𝒟[extractabilityGame model config 1 adversary] {tr | Drift model.view tr} =
      (1 : ENNReal) / 2 := by
  rw [game_law, Measure.map_apply (measurable_of_countable _) (by trivial)]
  have hevent : outcome ⁻¹' {tr | Drift model.view tr} = {false} := by
    ext reply
    cases reply <;> simp [drift_outcome_false, no_drift_outcome_true]
  rw [hevent, uniformOn_univ_apply_singleton]
  simp

theorem honestShared_probability : 𝒟[honestShared] {true} = 1 := by
  rw [honestShared_eq, bind_pure_comp, evalDist_map_of_discrete, evalDist_query_uniform]
  rw [Measure.map_apply (measurable_of_countable _) (MeasurableSet.singleton true)]
  have hevent : (fun _ : Bool => true) ⁻¹' ({true} : Set Bool) = Set.univ := by
    ext reply
    simp
  rw [hevent, measure_univ]

theorem honestReset_probability : 𝒟[honestReset] {true} = (1 : ENNReal) / 2 := by
  rw [honestReset_eq]
  rw [evalDist_bind_of_discrete]
  simp only [bind_pure_comp, evalDist_map_of_discrete, evalDist_query_uniform]
  rw [Measure.bind_apply (MeasurableSet.singleton true) (measurable_of_countable _).aemeasurable]
  have hinner (root : Bool) :
      (uniformOn (Set.univ : Set Bool)).map (fun reply => reply == root) {true} =
        (1 : ENNReal) / 2 := by
    rw [Measure.map_apply (measurable_of_countable _) (MeasurableSet.singleton true)]
    have hevent : (fun reply : Bool => reply == root) ⁻¹' {true} = {root} := by
      ext reply
      simp
    rw [hevent, uniformOn_univ_apply_singleton]
    simp
  simp only [hinner, lintegral_const, measure_univ, mul_one]


end MerkleCheckpoints
