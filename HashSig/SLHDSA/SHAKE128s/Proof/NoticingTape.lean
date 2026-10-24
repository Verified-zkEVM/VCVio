/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.TapeFactor
public import HashSig.SLHDSA.SHAKE128s.Proof.CoverageCount
import VCVio.OracleComp.EvalDist.Sum

/-!
# The tape factorisation at the recorder that notices

`evalDist_noticingSplitTapeRun_cont` factorises the two-recording run through two blocks drawn
in advance, with an arbitrary continuation on each side. The run is at
`RecorderView.noticingRecorderOf`: the recorder run at a state that has been told about the
query, so that a filing test may read something a cache hit would otherwise hide.

**It is the cache-view recorder's induction at a noticed state.** `noticingRecorderOf` is
*defined* as `recorderOf` run at the noticed carrier, so every step of the proof is the step of
the plain tape factorisation with `cache` replaced by `CacheView.onQuery cache input`. The notice
does not touch the cache (`RecorderView.cacheOf_onQuery`), so the freshness guard is unmoved;
what moves is only which state the two tests are read at, and the tests are arbitrary predicates
of the state.

The file has the recorder `noticingSplitTapeRecorder`, its step laws, the leave-one-out charge
stated over an arbitrary run with the selection's causality as a hypothesis, the continuation
forms of the factorisation and of the cell correspondences, and `blockRunOf`, the run with the
two blocks it read kept beside its result.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal


namespace SlhDsaSecurity.NoticingTape

variable {α γ : Type}

open DigestTape TapeFactor RecorderView

variable {σ : Type} [CacheView σ]

/-- **The two-headed tape recorder, told about every query.** The notice is applied to the
carrier before the step, exactly as `RecorderView.noticingRecorderOf` applies it before
`recorderOf`'s; the two blocks and the two recordings ride through untouched. -/
noncomputable def noticingSplitTapeRecorder (leftKeep rightKeep : Bytes → σ → Prop) :
    QueryImpl OracleWorld (StateT (SplitTapeState σ) ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => ((splitTapeRecorder leftKeep rightKeep) (Sum.inl coin)).run state
    | Sum.inr input =>
        ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
          (CacheView.onQuery state.1 input, state.2)

/-- A coin query to the noticing recorder is the tape recorder's coin step. -/
theorem noticingSplitTapeRecorder_run_inl (leftKeep rightKeep : Bytes → σ → Prop)
    (coin : unifSpec.Domain) (state : SplitTapeState σ) :
    ((noticingSplitTapeRecorder leftKeep rightKeep) (Sum.inl coin)).run state =
      ((splitTapeRecorder leftKeep rightKeep) (Sum.inl coin)).run state := rfl

/-- A hash query to the noticing recorder is the tape recorder's step at the noticed carrier. -/
theorem noticingSplitTapeRecorder_run_inr (leftKeep rightKeep : Bytes → σ → Prop)
    (input : Bytes) (state : SplitTapeState σ) :
    ((noticingSplitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run state =
      ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
        (CacheView.onQuery state.1 input, state.2) := rfl

/-! ## The step laws, and everything that follows from them alone

`rightOf` and `leftOf` read the recordings, which the notice does not touch, so
`rightOf (CacheView.onQuery state.1 input, state.2) = rightOf state` holds definitionally. That
is why the lemmas below are applications of the cache version rather than copies of it:
each is a statement about the recordings, and the notice is invisible to them. -/

open scoped Classical in
/-- **One step of the repaired recorder only extends the target recording.** -/
theorem noticingSplitTapeRecorder_step (leftKeep rightKeep : Bytes → σ → Prop)
    (queried : OracleWorld.Domain) (state : SplitTapeState σ) :
    ∀ step ∈ support (((noticingSplitTapeRecorder leftKeep rightKeep) queried).run state),
      rightOf state <+: rightOf step.2 := by
  classical
  rcases queried with coin | input
  · exact splitTapeRecorder_step leftKeep rightKeep (Sum.inl coin) state
  · rw [noticingSplitTapeRecorder_run_inr]
    exact splitTapeRecorder_step leftKeep rightKeep (Sum.inr input)
      (CacheView.onQuery state.1 input, state.2)

open scoped Classical in
/-- **The target recording only grows**, at the repaired recorder. -/
theorem noticingRightOf_prefix (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitTapeState σ)
    (result : α × SplitTapeState σ)
    (hmem : result ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
      computation).run state)) :
    rightOf state <+: rightOf result.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    exact List.IsPrefix.trans
      (noticingSplitTapeRecorder_step leftKeep rightKeep queried state step hstep)
      (ih step.1 step.2 result hrest)

open scoped Classical in
/-- **The disclosing recording only grows**, at the repaired recorder. -/
theorem noticingLeftOf_prefix (leftKeep rightKeep : Bytes → σ → Prop)
    {α : Type} (computation : OracleComp OracleWorld α) (state : SplitTapeState σ)
    (result : α × SplitTapeState σ)
    (hmem : result ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
      computation).run state)) :
    leftOf state <+: leftOf result.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine List.IsPrefix.trans ?_ (ih step.1 step.2 result hrest)
    rcases queried with coin | input
    · exact leftOf_step leftKeep rightKeep (Sum.inl coin) state step hstep
    · rw [noticingSplitTapeRecorder_run_inr] at hstep
      exact leftOf_step leftKeep rightKeep (Sum.inr input)
        (CacheView.onQuery state.1 input, state.2) step hstep

/-! ## The charge, with the run a parameter

The three lemmas the coverage charge is assembled from use only three things about the run:
that one cell of the target block may be redrawn, that the run's *selection* of that cell does
not see its value, and that a recorded entry is the block cell it came from. Only the second
mentions the run at all, and it is the one a new presentation has to prove.

So they are stated over an arbitrary `run`, with the selection's causality as a hypothesis; a
bracketed three-stage run supplies it from its own and gets the rest free. **Stating the charge
once means the rate and the index set are written once**: a second copy is a second place the
margin could be spent.
-/

/-- A run with the two blocks it read kept beside its result. -/
noncomputable def blockRunOf {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (leftLength rightLength : Nat) :
    ProbComp ((List HashOutput × List HashOutput) × ρ) :=
  padding leftLength >>= fun leftTape =>
    padding rightLength >>= fun rightTape =>
      (fun result => ((leftTape, rightTape), result)) <$> run leftTape rightTape

open scoped Classical in
/-- **The charge on one target cell**, at the repaired recorder. -/
theorem prob_selected_hit_le_of_causal {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (rightOfResult : ρ → Record)
    (leftLength rightLength index : Nat) (hindex : index < rightLength)
    (goodBlock : List HashOutput → Prop) (hit : List HashOutput → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr{let value ← ($ᵗ HashOutput : ProbComp HashOutput)}[hit leftTape value] ≤ rate)
    (hcausal : ∀ (leftTape rightTape : List HashOutput) (value : HashOutput),
      Pr{let z ← run leftTape (rightTape.set index value)}[index < (rightOfResult z).length] =
        Pr{let z ← run leftTape rightTape}[index < (rightOfResult z).length]) :
    Pr{let outcome ← blockRunOf run leftLength rightLength}[
          index < (rightOfResult outcome.2).length ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value] ≤
      Pr{let outcome ← blockRunOf run leftLength rightLength}[
          index < (rightOfResult outcome.2).length] * rate := by
  classical
  set target : List HashOutput → List HashOutput → ℝ≥0∞ := fun leftTape rightTape =>
    Pr{let result ← run leftTape rightTape}[index < (rightOfResult result).length] with htarget
  -- The selection alone, with the blocks forgotten.
  have hright : Pr{let outcome ← blockRunOf run leftLength rightLength}[
        index < (rightOfResult outcome.2).length] =
      ∑' leftTape, Pr{let x ← padding leftLength}[x = leftTape] *
        ∑' rightTape, Pr{let x ← padding rightLength}[x = rightTape] *
          target leftTape rightTape := by
    rw [blockRunOf, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun leftTape => congrArg _ ?_
    rw [OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun rightTape => congrArg _ ?_
    rw [prEvent_map]
  -- The charged event, after one cell of the target block is redrawn.
  have hleft : Pr{let outcome ← blockRunOf run leftLength rightLength}[
        index < (rightOfResult outcome.2).length ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value] =
      ∑' leftTape, Pr{let x ← padding leftLength}[x = leftTape] *
        ∑' rightTape, Pr{let x ← padding rightLength}[x = rightTape] *
          ∑' value, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = value] *
            Pr{let result ← run leftTape (rightTape.set index value)}[
                index < (rightOfResult result).length ∧ goodBlock leftTape ∧
                  ∃ other, (rightTape.set index value)[index]? = some other ∧
                    hit leftTape other] := by
    rw [blockRunOf]
    refine ((EvalDistEq.bind_right (padding leftLength) fun leftTape =>
      evalDist_padding_set rightLength index hindex
        fun rightTape => (fun result => ((leftTape, rightTape), result)) <$>
          run leftTape rightTape).prEvent_eq _).trans ?_
    rw [OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun leftTape => congrArg _ ?_
    rw [OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun rightTape => congrArg _ ?_
    rw [OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun value => congrArg _ ?_
    rw [prEvent_map]
  rw [hleft, hright, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun leftTape => ?_
  rw [mul_assoc, ← ENNReal.tsum_mul_right]
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun rightTape => ?_)
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  -- The cell's own draw is all that is left to charge.
  calc ∑' value, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = value] *
        Pr{let result ← run leftTape (rightTape.set index value)}[
            index < (rightOfResult result).length ∧ goodBlock leftTape ∧
              ∃ other, (rightTape.set index value)[index]? = some other ∧ hit leftTape other]
      ≤ ∑' value, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = value] *
          (if goodBlock leftTape ∧ hit leftTape value then target leftTape rightTape else 0) := by
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        refine le_trans (prEvent_mono _ _ (fun result : ρ =>
          (goodBlock leftTape ∧ hit leftTape value) ∧
            index < (rightOfResult result).length) ?_) ?_
        · rintro result ⟨hselected, hgood, other, hread, hhit⟩
          exact ⟨⟨hgood, (eq_of_getElem?_set rightTape index value other hread) ▸ hhit⟩,
            hselected⟩
        · rw [probEvent_const_and]
          by_cases hcase : goodBlock leftTape ∧ hit leftTape value
          · rw [ite_eq_left hcase, ite_eq_left hcase, htarget]
            exact le_of_eq (hcausal leftTape rightTape value)
          · rw [ite_eq_right hcase, ite_eq_right hcase]
    _ ≤ target leftTape rightTape * rate := by
        by_cases hgood : goodBlock leftTape
        · simp only [hgood, true_and]
          calc ∑' value, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = value] *
                (if hit leftTape value then target leftTape rightTape else 0)
              = (∑' value, if hit leftTape value then
                  Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = value] else 0) *
                  target leftTape rightTape := by
                rw [← ENNReal.tsum_mul_right]
                refine tsum_congr fun value => ?_
                by_cases hhit : hit leftTape value
                · rw [ite_eq_left hhit, ite_eq_left hhit]
                · rw [ite_eq_right hhit, ite_eq_right hhit, zero_mul, mul_zero]
            _ ≤ rate * target leftTape rightTape := by
                rw [← OracleComp.prEvent_eq_tsum_ite]
                exact mul_le_mul' (hrate leftTape hgood) le_rfl
            _ = _ := mul_comm _ _
        · simp only [hgood, false_and, ↓reduceIte, mul_zero, tsum_zero]
          exact zero_le

/-- The sum of the per-cell selection probabilities is an expected recording length. -/
theorem sum_prob_selected_le_expected_of {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (rightOfResult : ρ → Record)
    (leftLength rightLength : Nat) :
    (∑ index : Fin rightLength,
        Pr{let outcome ← blockRunOf run leftLength rightLength}[
          index.val < (rightOfResult outcome.2).length]) ≤
      ∑' outcome, Pr{let x ← blockRunOf run leftLength rightLength}[x = outcome] *
        (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞) := by
  classical
  calc ∑ index : Fin rightLength,
        Pr{let outcome ← blockRunOf run leftLength rightLength}[
          index.val < (rightOfResult outcome.2).length]
      = ∑ index : Fin rightLength, ∑' outcome,
          (if index.val < (rightOfResult outcome.2).length then
            Pr{let x ← blockRunOf run leftLength rightLength}[x = outcome]
          else 0) :=
        Finset.sum_congr rfl fun index _ => OracleComp.prEvent_eq_tsum_ite _ _
    _ = ∑' outcome, ∑ index : Fin rightLength,
          (if index.val < (rightOfResult outcome.2).length then
            Pr{let x ← blockRunOf run leftLength rightLength}[x = outcome]
          else 0) := sum_tsum_comm Finset.univ _
    _ ≤ ∑' outcome, Pr{let x ← blockRunOf run leftLength rightLength}[x = outcome] *
          (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun outcome => ?_
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
          mul_comm]
        refine mul_le_mul' le_rfl (Nat.cast_le.mpr ?_)
        have hinject := Finset.card_le_card_of_injOn (fun index : Fin rightLength => index.val)
          (s := Finset.univ.filter
            (fun index : Fin rightLength => index.val < (rightOfResult outcome.2).length))
          (t := Finset.range (rightOfResult outcome.2).length)
          (fun index hindex => Finset.mem_range.mpr (by simpa using hindex))
          (fun left _ right _ hvalue => Fin.val_injective hvalue)
        simpa using hinject

open scoped Classical in
/-- **The coverage charge, as an expectation**, at the repaired recorder. This is what the
carrier's answer run composes with. -/
theorem prob_exists_hit_le_expected_of_causal {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (rightOfResult : ρ → Record)
    (leftLength rightLength : Nat)
    (goodBlock : List HashOutput → Prop) (hit : List HashOutput → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr{let value ← ($ᵗ HashOutput : ProbComp HashOutput)}[hit leftTape value] ≤ rate)
    (hcausal : ∀ (index : Nat) (leftTape rightTape : List HashOutput)
        (value : HashOutput),
      Pr{let z ← run leftTape (rightTape.set index value)}[index < (rightOfResult z).length] =
        Pr{let z ← run leftTape rightTape}[index < (rightOfResult z).length]) :
    Pr{let outcome ← blockRunOf run leftLength rightLength}[
            ∃ index : Fin rightLength, index.val < (rightOfResult outcome.2).length ∧
            goodBlock outcome.1.1 ∧
            ∃ value, outcome.1.2[index.val]? = some value ∧ hit outcome.1.1 value] ≤
      (∑' outcome, Pr{let x ← blockRunOf run leftLength rightLength}[x = outcome] *
        (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞)) * rate := by
  classical
  refine le_trans (prEvent_mono _ _ (fun outcome => ∃ index ∈ (Finset.univ :
      Finset (Fin rightLength)), index.val < (rightOfResult outcome.2).length ∧
      goodBlock outcome.1.1 ∧
      ∃ value, outcome.1.2[index.val]? = some value ∧ hit outcome.1.1 value)
    fun outcome hhit => by
      obtain ⟨index, hindex⟩ := hhit
      exact ⟨index, Finset.mem_univ index, hindex⟩) ?_
  refine le_trans (prEvent_exists_finset_le _ _ _) ?_
  refine le_trans (Finset.sum_le_sum fun index _ =>
    prob_selected_hit_le_of_causal run rightOfResult leftLength rightLength
      index.val
      index.isLt goodBlock hit rate hrate (hcausal index.val)) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul' (sum_prob_selected_le_expected_of run rightOfResult
    leftLength rightLength) le_rfl

/-! ## The factorisation with a continuation, which is what composes

The carrier's tail is three runs, and the middle one contains a *nested* run: the signer's own
queries, simulated through the same handler between two bracket points. A one-run factorisation
cannot be chained: after a run has consumed part of a block, what is left is a block of a length
the run itself chose, so the next stage cannot draw a fresh one and cannot be handed the
remainder as data either.

The fix is to make the continuation a parameter on both sides and to demand of it **exactly what
the conclusion gives**: that it factorises against freshly drawn blocks, at every pair of
lengths. The statement then composes with itself — the hypothesis of the composite is the
conclusion of the tail — and the `pure` case is the hypothesis applied once rather than a
dropped block.

**Blocks are drawn once, at the top.** That is not an optimisation. Three stages each drawing
their own block would give the per-cell charge three index sets instead of one, and the counting
step in `sum_prob_selected_le_expected_of` would be summing over a different thing. Drawn
once and threaded, the index set stays `Fin rightLength` over one block and the rate stays the
per-cell one. -/

open scoped Classical in
/-- **The tape factorisation with an arbitrary continuation on each side.** The hypothesis is
the conclusion's own shape at the continuation, which is what lets this be used at a nested run:
the outer induction supplies `hafter` and this supplies the inner run. -/
theorem evalDist_noticingSplitTapeRun_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (handlerAfter : α × StateOf σ → ProbComp γ)
    (tapeAfter : α × SplitTapeState σ → ProbComp γ)
    (hafter : ∀ (leftLength rightLength : Nat) (z : α × StateOf σ),
      handlerAfter z =ᵈ
        (padding leftLength >>= fun leftTape => padding rightLength >>= fun rightTape =>
            tapeAfter (z.1, (z.2.1, (leftTape, rightTape), z.2.2)))) :
    ∀ (leftLength rightLength : Nat) (cache : σ) (leftRecord rightRecord : Record),
      (simulateQ (noticingRecorderOf leftKeep rightKeep) computation).run
          (cache, leftRecord, rightRecord) >>= handlerAfter =ᵈ
        (padding leftLength >>= fun leftTape =>
            padding rightLength >>= fun rightTape =>
              (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
                  (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= tapeAfter) := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro leftLength rightLength cache leftRecord rightRecord
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hafter leftLength rightLength (value, (cache, leftRecord, rightRecord))
  | query_bind queried next ih =>
    intro leftLength rightLength cache leftRecord rightRecord
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases queried with coin | input
    · simp only [noticingRecorderOf_run_inl, noticingSplitTapeRecorder_run_inl,
        RecorderView.recorderOf_run_inl, splitTapeRecorder_run_inl, bind_assoc, pure_bind]
      refine (EvalDistEq.bind_right _
        (fun value => ih value leftLength rightLength cache leftRecord rightRecord)).trans ?_
      exact evalDist_comm_blocks _ leftLength rightLength _
    · rw [noticingRecorderOf_run_inr leftKeep rightKeep input (cache, leftRecord, rightRecord)]
      rw [show (fun leftTape : List HashOutput => padding rightLength >>= fun rightTape =>
            ((noticingSplitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
                (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= fun step =>
              (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
                (next step.1)).run step.2 >>= tapeAfter) =
          fun leftTape : List HashOutput => padding rightLength >>= fun rightTape =>
            ((splitTapeRecorder leftKeep rightKeep) (Sum.inr input)).run
                (CacheView.onQuery cache input, (leftTape, rightTape),
                  (leftRecord, rightRecord)) >>= fun step =>
              (simulateQ (noticingSplitTapeRecorder leftKeep rightKeep)
                (next step.1)).run step.2 >>= tapeAfter from by
        funext leftTape
        refine congrArg (fun step => padding rightLength >>= step) ?_
        funext rightTape
        rw [noticingSplitTapeRecorder_run_inr]]
      set noticed : σ := CacheView.onQuery cache input with hnoticed
      by_cases hfresh : CacheView.cacheOf noticed input = none
      · by_cases hleft : leftKeep input noticed
        · simp only [splitRecorder_run_left leftKeep rightKeep input noticed leftRecord
            rightRecord hfresh hleft, bind_assoc, pure_bind]
          cases leftLength with
          | zero =>
            simp only [padding_zero_bind,
              splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed _ leftRecord
                rightRecord hfresh hleft, bind_assoc, pure_bind]
            refine (EvalDistEq.bind_right _
              (fun value : HashOutput =>
                ih value 0 rightLength (CacheView.update noticed input value)
                  (leftRecord ++ [(input, value)]) rightRecord)).trans ?_
            simp only [padding_zero_bind]
            exact OracleComp.EvalDistEq.bind_bind_swap _ (padding rightLength) _
          | succ remaining =>
            simp only [padding_succ_bind,
              splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed _ _ _ leftRecord
                rightRecord hfresh hleft, pure_bind]
            exact EvalDistEq.bind_right _
              fun value : HashOutput => ih value remaining rightLength
                (CacheView.update noticed input value)
                (leftRecord ++ [(input, value)]) rightRecord
        · by_cases hright : rightKeep input noticed
          · simp only [splitRecorder_run_right leftKeep rightKeep input noticed leftRecord
              rightRecord hfresh hleft hright, bind_assoc, pure_bind]
            cases rightLength with
            | zero =>
              simp only [padding_zero_bind,
                splitTapeRecorder_run_right_nil leftKeep rightKeep input noticed _ leftRecord
                  rightRecord hfresh hleft hright, bind_assoc, pure_bind]
              refine (EvalDistEq.bind_right _
                (fun value : HashOutput =>
                  ih value leftLength 0 (CacheView.update noticed input value)
                    leftRecord (rightRecord ++ [(input, value)]))).trans ?_
              simp only [padding_zero_bind]
              exact OracleComp.EvalDistEq.bind_bind_swap _ (padding leftLength) _
            | succ remaining =>
              simp only [padding_succ_bind,
                splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed _ _ _
                  leftRecord rightRecord hfresh hleft hright, pure_bind]
              refine (EvalDistEq.bind_right _
                (fun value : HashOutput => ih value leftLength remaining
                  (CacheView.update noticed input value)
                  leftRecord (rightRecord ++ [(input, value)]))).trans ?_
              exact OracleComp.EvalDistEq.bind_bind_swap _ (padding leftLength) _
          · simp only [splitRecorder_run_other leftKeep rightKeep input noticed
              (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2),
              splitTapeRecorder_run_other leftKeep rightKeep input noticed _
                (leftRecord, rightRecord) (fun h => hleft h.2) (fun h => hright h.2),
              bind_assoc, pure_bind]
            refine (EvalDistEq.bind_right _
              (fun step : HashOutput × σ => ih step.1 leftLength rightLength step.2 leftRecord
                rightRecord)).trans ?_
            exact evalDist_comm_blocks _ leftLength rightLength _
      · simp only [splitRecorder_run_other leftKeep rightKeep input noticed
          (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          splitTapeRecorder_run_other leftKeep rightKeep input noticed _
            (leftRecord, rightRecord) (fun h => hfresh h.1) (fun h => hfresh h.1),
          bind_assoc, pure_bind]
        refine (EvalDistEq.bind_right _
          (fun step : HashOutput × σ =>
            ih step.1 leftLength rightLength step.2 leftRecord rightRecord)).trans ?_
        exact evalDist_comm_blocks _ leftLength rightLength _

/-! ## The selection's causality, with a continuation

A run's selection of a target cell must not see that cell's value. The bracketed tail is three
runs, and after the first stage the two sides are in different states, so the second stage's
probability is not the same object on both sides. The continuation is a parameter, and what is
asked of it is **the conclusion's own shape** — that its selection does not see the cell either —
plus one fact that composes by itself: it never shortens the target recording. The `pure` case
is then the continuation's own causality rather than a termination, and the step that *reads*
the cell is settled on both sides by the recording already being long enough, exactly as
before.
-/

open scoped Classical in
/-- **Once the recording is long enough the whole rest of the run keeps it so.** The
continuation form of the single-run statement: the run only grows the recording and the
continuation only grows it further. -/
theorem probEvent_length_eq_one_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (after : α × SplitTapeState σ → ProbComp γ) (finalRight : γ → Record)
    (hgrow : ∀ (z : α × SplitTapeState σ) (w : γ), w ∈ support (after z) ->
      (rightOf z.2).length ≤ (finalRight w).length)
    (cache : σ) (tapes : List HashOutput × List HashOutput)
    (leftRecord rightRecord : Record) (entry : Bytes × HashOutput) (bound : Nat)
    (hbound : bound < (rightRecord ++ [entry]).length) :
    Pr{let w ← ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
          (cache, tapes, (leftRecord, rightRecord ++ [entry])) >>= after)}[
        bound < (finalRight w).length] = 1 := by
  classical
  refine prEvent_eq_one_of_forall_mem_support _ _ fun w hw => ?_
  rw [mem_support_bind_iff] at hw
  obtain ⟨z, hz, hafterMem⟩ := hw
  have hprefix := noticingRightOf_prefix leftKeep rightKeep computation
    (cache, tapes, (leftRecord, rightRecord ++ [entry])) z hz
  exact lt_of_lt_of_le (lt_of_lt_of_le hbound hprefix.length_le) (hgrow z w hafterMem)

/-! ## The cell correspondence, with a continuation

The correspondence relates the **final** recording at offset `rightRecord.length + index` to the
**starting** block at `index`. The hypothesis is the conclusion at the continuation's *own*
starting recording and block, so no global index arithmetic ever appears: the outer layer
relates the original offsets to the intermediate ones, the inner layer relates the intermediate
ones to the final, and nothing has to count how many cells the first stage ate.
-/

/-- The unread remainder of the target block. -/
def rightTapeOf (state : SplitTapeState σ) : List HashOutput := state.2.1.2

open scoped Classical in
/-- **Each recorded target answer is the block cell it was read from**, with a continuation. -/
theorem rightOf_getElem?_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (after : α × SplitTapeState σ → ProbComp γ)
    (finalRight : γ → Record)
    (hprefix : ∀ (z : α × SplitTapeState σ) (w : γ),
      w ∈ support (after z) → rightOf z.2 <+: finalRight w)
    (hafter : ∀ (z : α × SplitTapeState σ) (w : γ),
      w ∈ support (after z) → ∀ index : Nat,
        (rightOf z.2).length + index < (finalRight w).length ->
        index < (rightTapeOf z.2).length ->
          ((finalRight w)[(rightOf z.2).length + index]?).map Prod.snd =
            (rightTapeOf z.2)[index]?) :
    ∀ (cache : σ) (leftTape rightTape : List HashOutput)
      (leftRecord rightRecord : Record) (w : γ),
      w ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= after) ->
      ∀ index : Nat, rightRecord.length + index < (finalRight w).length ->
        index < rightTape.length ->
        ((finalRight w)[rightRecord.length + index]?).map Prod.snd = rightTape[index]? := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache leftTape rightTape leftRecord rightRecord w hw index hreached hcell
    rw [simulateQ_pure, StateT.run_pure, pure_bind] at hw
    exact hafter (value, (cache, (leftTape, rightTape), (leftRecord, rightRecord))) w hw index
      hreached hcell
  | query_bind queried next ih =>
    intro cache leftTape rightTape leftRecord rightRecord w hw index hreached hcell
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
      mem_support_bind_iff] at hw
    obtain ⟨step, hstep, hrest⟩ := hw
    rcases queried with coin | input
    · rw [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl,
        mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure] at hrest
      exact ih _ _ _ _ _ _ w hrest index hreached hcell
    · rw [noticingSplitTapeRecorder_run_inr] at hstep
      set noticed : σ := CacheView.onQuery cache input with hnoticed
      by_cases hfresh : CacheView.cacheOf noticed input = none
      · by_cases hleft : leftKeep input noticed
        · cases leftTape with
          | nil =>
            rw [splitTapeRecorder_run_left_nil leftKeep rightKeep input noticed rightTape
              leftRecord rightRecord hfresh hleft, mem_support_bind_iff] at hstep
            obtain ⟨answer, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure] at hrest
            exact ih _ _ _ _ _ _ w hrest index hreached hcell
          | cons head rest =>
            rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest
              rightTape leftRecord rightRecord hfresh hleft, support_pure,
              Set.mem_singleton_iff] at hstep
            rw [hstep] at hrest
            exact ih _ _ _ _ _ _ w hrest index hreached hcell
        · by_cases hright : rightKeep input noticed
          · cases rightTape with
            | nil => exact absurd hcell (by simp)
            | cons head rest =>
              rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head
                rest leftRecord rightRecord hfresh hleft hright, support_pure,
                Set.mem_singleton_iff] at hstep
              rw [hstep] at hrest
              cases index with
              | zero =>
                rw [mem_support_bind_iff] at hrest
                obtain ⟨inner, hinner, hw2⟩ := hrest
                have hmid := noticingRightOf_prefix leftKeep rightKeep (next head)
                  (CacheView.update noticed input head, (leftTape, rest),
                    (leftRecord, rightRecord ++ [(input, head)])) inner hinner
                have hall : rightRecord ++ [(input, head)] <+: finalRight w :=
                  List.IsPrefix.trans hmid (hprefix inner w hw2)
                rw [Nat.add_zero]
                rw [getElem?_of_prefix hall rightRecord.length (by simp)]
                simp
              | succ smaller =>
                have hstep' := ih _ _ _ _ _ _ w hrest smaller
                  (by simpa using (by omega : rightRecord.length + 1 + smaller <
                    (finalRight w).length))
                  (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hcell))
                rw [show rightRecord.length + (smaller + 1) =
                    (rightRecord ++ [(input, head)]).length + smaller from by simp; omega]
                rw [hstep']
                simp
          · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
              (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hleft h.2)
              (fun h => hright h.2), mem_support_bind_iff] at hstep
            obtain ⟨answer, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure] at hrest
            exact ih _ _ _ _ _ _ w hrest index hreached hcell
      · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
          (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hfresh h.1)
          (fun h => hfresh h.1), mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure] at hrest
        exact ih _ _ _ _ _ _ w hrest index hreached hcell

/-- The unread remainder of the disclosing block. -/
def leftTapeOf (state : SplitTapeState σ) : List HashOutput := state.2.1.1

open scoped Classical in
/-- **Each recorded disclosing answer is the block cell it was read from**, with a continuation.
The mirror of `rightOf_getElem?_cont`. The two sides are not one lemma: the recorder's branches
differ in which block they consume and which recording they file, so a side-parameterised
version would have to swap the branch cases rather than abstract them. -/
theorem leftOf_getElem?_cont (leftKeep rightKeep : Bytes → σ → Prop)
    {α γ : Type} (computation : OracleComp OracleWorld α)
    (after : α × SplitTapeState σ → ProbComp γ)
    (finalLeft : γ → Record)
    (hprefix : ∀ (z : α × SplitTapeState σ) (w : γ),
      w ∈ support (after z) → leftOf z.2 <+: finalLeft w)
    (hafter : ∀ (z : α × SplitTapeState σ) (w : γ),
      w ∈ support (after z) → ∀ index : Nat,
        (leftOf z.2).length + index < (finalLeft w).length →
        index < (leftTapeOf z.2).length →
          ((finalLeft w)[(leftOf z.2).length + index]?).map Prod.snd =
            (leftTapeOf z.2)[index]?) :
    ∀ (cache : σ) (leftTape rightTape : List HashOutput)
      (leftRecord rightRecord : Record) (w : γ),
      w ∈ support ((simulateQ (noticingSplitTapeRecorder leftKeep rightKeep) computation).run
        (cache, (leftTape, rightTape), (leftRecord, rightRecord)) >>= after) →
      ∀ index : Nat, leftRecord.length + index < (finalLeft w).length →
        index < leftTape.length →
        ((finalLeft w)[leftRecord.length + index]?).map Prod.snd = leftTape[index]? := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro cache leftTape rightTape leftRecord rightRecord w hw index hreached hcell
    rw [simulateQ_pure, StateT.run_pure, pure_bind] at hw
    exact hafter (value, (cache, (leftTape, rightTape), (leftRecord, rightRecord))) w hw index
      hreached hcell
  | query_bind queried next ih =>
    intro cache leftTape rightTape leftRecord rightRecord w hw index hreached hcell
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc,
      mem_support_bind_iff] at hw
    obtain ⟨step, hstep, hrest⟩ := hw
    rcases queried with coin | input
    · rw [noticingSplitTapeRecorder_run_inl, splitTapeRecorder_run_inl,
        mem_support_bind_iff] at hstep
      obtain ⟨answer, -, hpure⟩ := hstep
      rw [support_pure, Set.mem_singleton_iff] at hpure
      rw [hpure] at hrest
      exact ih _ _ _ _ _ _ w hrest index hreached hcell
    · rw [noticingSplitTapeRecorder_run_inr] at hstep
      set noticed : σ := CacheView.onQuery cache input with hnoticed
      by_cases hfresh : CacheView.cacheOf noticed input = none
      · by_cases hleft : leftKeep input noticed
        · cases leftTape with
          | nil => exact absurd hcell (by simp)
          | cons head rest =>
            rw [splitTapeRecorder_run_left_cons leftKeep rightKeep input noticed head rest
              rightTape leftRecord rightRecord hfresh hleft, support_pure,
              Set.mem_singleton_iff] at hstep
            rw [hstep] at hrest
            cases index with
            | zero =>
              rw [mem_support_bind_iff] at hrest
              obtain ⟨inner, hinner, hw2⟩ := hrest
              have hmid := noticingLeftOf_prefix leftKeep rightKeep (next head)
                (CacheView.update noticed input head, (rest, rightTape),
                  (leftRecord ++ [(input, head)], rightRecord)) inner hinner
              have hall : leftRecord ++ [(input, head)] <+: finalLeft w :=
                List.IsPrefix.trans hmid (hprefix inner w hw2)
              rw [Nat.add_zero]
              rw [getElem?_of_prefix hall leftRecord.length (by simp)]
              simp
            | succ smaller =>
              have hstep' := ih _ _ _ _ _ _ w hrest smaller
                (by simpa using (by omega : leftRecord.length + 1 + smaller <
                  (finalLeft w).length))
                (by simpa using Nat.lt_of_succ_lt_succ (by simpa using hcell))
              rw [show leftRecord.length + (smaller + 1) =
                  (leftRecord ++ [(input, head)]).length + smaller from by simp; omega]
              rw [hstep']
              simp
        · by_cases hright : rightKeep input noticed
          · cases rightTape with
            | nil =>
              rw [splitTapeRecorder_run_right_nil leftKeep rightKeep input noticed leftTape
                leftRecord rightRecord hfresh hleft hright, mem_support_bind_iff] at hstep
              obtain ⟨answer, -, hpure⟩ := hstep
              rw [support_pure, Set.mem_singleton_iff] at hpure
              rw [hpure] at hrest
              exact ih _ _ _ _ _ _ w hrest index hreached hcell
            | cons head rest =>
              rw [splitTapeRecorder_run_right_cons leftKeep rightKeep input noticed leftTape head
                rest leftRecord rightRecord hfresh hleft hright, support_pure,
                Set.mem_singleton_iff] at hstep
              rw [hstep] at hrest
              exact ih _ _ _ _ _ _ w hrest index hreached hcell
          · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
              (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hleft h.2)
              (fun h => hright h.2), mem_support_bind_iff] at hstep
            obtain ⟨answer, -, hpure⟩ := hstep
            rw [support_pure, Set.mem_singleton_iff] at hpure
            rw [hpure] at hrest
            exact ih _ _ _ _ _ _ w hrest index hreached hcell
      · rw [splitTapeRecorder_run_other leftKeep rightKeep input noticed
          (leftTape, rightTape) (leftRecord, rightRecord) (fun h => hfresh h.1)
          (fun h => hfresh h.1), mem_support_bind_iff] at hstep
        obtain ⟨answer, -, hpure⟩ := hstep
        rw [support_pure, Set.mem_singleton_iff] at hpure
        rw [hpure] at hrest
        exact ih _ _ _ _ _ _ w hrest index hreached hcell

open scoped Classical in
/-- **A supported outcome of a blocked run is a supported run against its own two blocks.** -/
theorem mem_support_blockRunOf {ρ : Type}
    (run : List HashOutput → List HashOutput → ProbComp ρ)
    (leftLength rightLength : Nat)
    (outcome : (List HashOutput × List HashOutput) × ρ)
    (hmem : outcome ∈ support (blockRunOf run leftLength rightLength)) :
    outcome.1.1 ∈ support (padding leftLength) ∧
      outcome.1.2 ∈ support (padding rightLength) ∧
        outcome.2 ∈ support (run outcome.1.1 outcome.1.2) := by
  rw [blockRunOf, mem_support_bind_iff] at hmem
  obtain ⟨leftTape, hleftTape, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨rightTape, hrightTape, hinner⟩ := hrest
  rw [support_map] at hinner
  obtain ⟨result, hresult, hshape⟩ := hinner
  rw [← hshape]
  exact ⟨hleftTape, hrightTape, hresult⟩

end SlhDsaSecurity.NoticingTape
