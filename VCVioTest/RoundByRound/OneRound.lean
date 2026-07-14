/-
Copyright (c) 2026 Aristotle (Harmonic), Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/
import VCVio.CryptoFoundations.RoundByRound

/-!
# One-round regression for round-by-round knowledge extraction

This smoke test instantiates a genuinely nontrivial one-round `KnowledgeExtractionFamily` over a
uniformly sampled two-challenge round and exercises the strict-trigger content of Definition 3.12
of Block, Garreta, Tiwari, and Zając (*On Soundness Notions for Interactive Oracle Proofs*,
Cryptology ePrint Archive 2023/1256), rather than merely naming the generic bridge.

The instantiated family is deliberately non-vacuous:

* the canonical initial context is doomed for every input (`oneRound_initialCondition`);
* a doomed terminal context forces rejection (`oneRound_terminalCondition`);
* the extracted witness genuinely fails the relation (`oneRound_relation_fails`);
* the fresh challenge escapes the doomed set with probability exactly `1 / 2`
  (`oneRound_escape_prob`), so escape has nonzero probability;
* on the doomed `(context, message)` subtype the transition `badEvent` reduces to that escape event
  (`oneRound_badEvent_iff`);
* at `error = Pr[escape] = 1 / 2` the strict trigger `error < Pr[escape]` does **not** fire, and
  both sides of the bridge hold (`oneRound_extractionCondition_half`, `oneRound_isBounded_half`);
* at the strictly smaller `error = 0` the strict trigger fires on a failed extraction, so both the
  extraction condition and boundedness fail (`oneRound_not_extractionCondition_zero`,
  `oneRound_not_isBounded_zero`).

At least one theorem (`oneRound_escape_prob`) establishes the concrete probability fact directly
instead of restating `KnowledgeExtractionFamily.extractionCondition_iff_isBounded` by application.
The final `oneRound_extractionCondition_iff_isBounded` still exercises the generic bridge on this
concrete family.
-/

open scoped ENNReal

namespace VCVioTest.RoundByRound

open _root_.RoundByRound
open OracleComp OracleSpec

/-- A genuinely nontrivial one-round knowledge-extraction family.

The context type at each stage is `Fin 2` (carrying the sampled challenge at the terminal stage),
the fresh challenge is sampled uniformly from `Fin 2`, and the doomed set is "stage `0`, or the
carried value is `0`". Thus the initial context is always doomed, the terminal context escapes doom
exactly when the sampled challenge is `1`, and the extractor returns `false` while the relation
only accepts `true`, so the extracted witness always fails the relation. -/
noncomputable def oneRound : KnowledgeExtractionFamily 1 where
  Statement := Unit
  Witness := Bool
  Context := fun _ => Fin 2
  Message := fun _ => Unit
  Challenge := fun _ => Fin 2
  FinalMessage := Unit
  challengeSampleable := fun _ => inferInstance
  statement := fun _ _ => ()
  initialContext := fun _ => 0
  extend := fun _ _ _ challenge => challenge
  statement_initial := fun _ => rfl
  statement_extend := fun _ _ _ _ => rfl
  doomed := fun stage c => stage = 0 ∨ c = 0
  extract := fun _ _ _ => false
  relation := fun _ w => w = true
  rejects := fun ctx _ => ctx = 0

/-- Regression for the PR #475 API break: the specialized
`OracleComp.probOutput_eq_sub_probFailure_of_unit` must still accept the public named argument
`spec := …`. -/
example {ι : Type} {spec : OracleSpec ι} [IsProbabilitySpec spec] (oa : OracleComp spec PUnit) :
    Pr[= () | oa] = 1 - Pr[⊥ | oa] :=
  probOutput_eq_sub_probFailure_of_unit (spec := spec)

/-- The canonical initial context is doomed for every input. -/
theorem oneRound_initialCondition : oneRound.InitialCondition := by
  intro _; exact Or.inl rfl

/-- A doomed terminal context forces the verifier to reject every final prover message. -/
theorem oneRound_terminalCondition : oneRound.TerminalCondition := by
  intro context _ hdoomed
  rcases hdoomed with h | h
  · exact absurd h (by decide)
  · exact h

/-- The directly extracted witness genuinely fails the relation. -/
theorem oneRound_relation_fails (context : oneRound.Context (0 : Fin 1).castSucc)
    (message : oneRound.Message 0) :
    ¬ oneRound.relation (oneRound.statement (0 : Fin 1).castSucc context)
        (oneRound.extract 0 context message) := by
  simp only [oneRound]; decide

/-- The fresh challenge escapes the doomed set with probability exactly `1 / 2`. This is the
concrete probability fact, proved directly rather than through the generic bridge. -/
theorem oneRound_escape_prob (context : oneRound.Context (0 : Fin 1).castSucc)
    (message : oneRound.Message 0) :
    Pr[oneRound.escapeEvent 0 context message | oneRound.sampleChallenge 0] = 1 / 2 := by
  have hev : Pr[oneRound.escapeEvent 0 context message | $ᵗ (Fin 2)]
      = Pr[(fun c : Fin 2 => c ≠ 0) | $ᵗ (Fin 2)] := by
    refine probEvent_ext (fun c _ => ?_)
    fin_cases c <;> simp only [KnowledgeExtractionFamily.escapeEvent, oneRound] <;> decide
  -- Normalize the dependent challenge type `oneRound.Challenge 0` to the concrete sampler
  -- `$ᵗ (Fin 2)` definitionally, so the subsequent rewrites never cross the unresolved
  -- dependent abbreviation (which fails under Lean 4.31 tactic instance transparency).
  change Pr[oneRound.escapeEvent 0 context message | $ᵗ (Fin 2)] = 1 / 2
  rw [hev, probEvent_uniformSample]
  have hc : (Finset.univ.filter (fun c : Fin 2 => c ≠ 0)).card = 1 := by decide
  rw [hc, Fintype.card_fin]
  norm_num

/-- On the doomed `(context, message)` subtype, the transition `badEvent` reduces exactly to the
escape event (because the extracted witness always fails the relation). -/
theorem oneRound_badEvent_iff (context : oneRound.Context (0 : Fin 1).castSucc)
    (message : oneRound.Message 0)
    (hdoomed : oneRound.doomed (0 : Fin 1).castSucc context) (challenge : oneRound.Challenge 0) :
    oneRound.toKnowledgeTransitionFamily.badEvent 0 ⟨(context, message), hdoomed⟩ challenge
      ↔ oneRound.escapeEvent 0 context message challenge := by
  rw [oneRound.toKnowledgeTransitionFamily_badEvent_iff 0 context message hdoomed challenge]
  exact ⟨fun h => h.2, fun h => ⟨oneRound_relation_fails context message, h⟩⟩

/-- Direct fact: the doomed-subtype transition family is bounded by the constant error `1 / 2`,
i.e. at `error = Pr[escape]` boundedness holds. -/
theorem oneRound_isBounded_half :
    oneRound.toKnowledgeTransitionFamily.IsBounded (fun _ => 1 / 2) := by
  rw [KnowledgeTransitionFamily.isBounded_iff]
  intro round cm
  obtain rfl : round = 0 := Subsingleton.elim _ _
  obtain ⟨⟨context, message⟩, hdoomed⟩ := cm
  rw [oneRound.probEvent_toKnowledgeTransitionFamily_badEvent_of_not_relation 0 context message
      hdoomed (oneRound_relation_fails context message), oneRound_escape_prob context message]

/-- At `error = Pr[escape] = 1 / 2` the strict trigger does not fire, so the extraction condition
holds; obtained from `oneRound_isBounded_half` through the generic bridge. -/
theorem oneRound_extractionCondition_half : oneRound.ExtractionCondition (fun _ => 1 / 2) :=
  (oneRound.extractionCondition_iff_isBounded _).mpr oneRound_isBounded_half

/-- Direct fact: the doomed-subtype transition family is **not** bounded by the strictly smaller
constant error `0`, because escape (hence the bad event) has probability `1 / 2 > 0`. -/
theorem oneRound_not_isBounded_zero :
    ¬ oneRound.toKnowledgeTransitionFamily.IsBounded (fun _ => 0) := by
  rw [KnowledgeTransitionFamily.isBounded_iff]
  push Not
  refine ⟨0, ⟨((0 : Fin 2), ()), Or.inl rfl⟩, ?_⟩
  rw [oneRound.probEvent_toKnowledgeTransitionFamily_badEvent_of_not_relation 0 (0 : Fin 2) ()
      (Or.inl rfl) (oneRound_relation_fails (0 : Fin 2) ()), oneRound_escape_prob (0 : Fin 2) ()]
  exact ENNReal.half_pos (by norm_num)

/-- At the strictly smaller `error = 0` the strict trigger fires on a failed extraction, so the
extraction condition fails; obtained from `oneRound_not_isBounded_zero` through the generic
bridge. -/
theorem oneRound_not_extractionCondition_zero : ¬ oneRound.ExtractionCondition (fun _ => 0) := by
  rw [oneRound.extractionCondition_iff_isBounded]
  exact oneRound_not_isBounded_zero

/-- Regression: the extensional extraction condition for `oneRound` is equivalent to boundedness of
its doomed `(context, message)` knowledge-transition family, i.e. the compiled instance of the
generic bridge `KnowledgeExtractionFamily.extractionCondition_iff_isBounded` on this concrete
family. -/
theorem oneRound_extractionCondition_iff_isBounded (error : Fin 1 → ℝ≥0∞) :
    oneRound.ExtractionCondition error ↔
      oneRound.toKnowledgeTransitionFamily.IsBounded error :=
  oneRound.extractionCondition_iff_isBounded error

end VCVioTest.RoundByRound
