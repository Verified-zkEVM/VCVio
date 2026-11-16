/-
Copyright (c) 2026 Alexander Hicks, Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Tom Wambsgans
-/

module

public import VCVio.OracleComp.ProbComp.IndepProductEvents
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection
public import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Sum

/-!
# The answer tape of a lazy random oracle

`tapeCachingImpl D R` answers like the lazy random oracle `OracleSpec.randomOracle`, except that
its fresh answers are taken in order off a list supplied ahead of time, falling back to fresh
uniform sampling once the list runs out. Averaged over a list of `m` independent uniform values
it *is* the lazy random oracle, jointly in the output and the final cache
(`evalDist_run_randomOracle_eq_tapeList`). Unlike the full-table identification of
`EagerTable.lean`, which pre-samples an answer for every point of the domain, the tape exposes
the *order* in which fresh answers were produced, and so has one independent coordinate per
fresh answer rather than one per domain point. That is what turns a statement about the tuple of
fresh answers — a product bound of `IndepProductEvents.lean` — into a statement about a
random-oracle run (`evalDist_run_randomOracle_setOf_le_of_transport`, and
`prEvent_run_randomOracle_le_of_transport` for an event observed in `Prop`, which needs no
measurable space on `R`).

Transporting an event of the final cache back to an event of the tape needs to know which tape
position each cache entry came from. `positionAux` instruments the tape state with that
bookkeeping: a position map `D → Option ℕ` and a count of the tape entries consumed.
`PositionInv` is the invariant its run maintains, and
`exists_pos_of_mem_support_run_tapeCachingImpl` is the consequence a caller wants: if the final
cache has at most `q` entries — the query bound, in the `QueryCache.enncard ≤ q` shape — then
every cache entry of a run on a length-`q` tape carries the tape value at its own position, and
distinct cache entries sit at distinct positions. The cache bound is what rules out the
fallback answers, which are not tape values: an off-tape answer requires the tape to have run
out first, hence `q + 1` cache entries.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace AnswerTape

section TapeDraw

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-! ## The tape draw, as a list -/

/-- `m` independent uniform draws from `R`, collected as a list. -/
noncomputable def tapeList (R : Type) [SampleableType R] (m : ℕ) : ProbComp (List R) :=
  List.ofFn <$> answerTape R m

/-- `tapeList` is `answerTape` read as a list. This is `tapeList`'s definition, published as
an equation because the definition itself is not exposed. -/
theorem tapeList_eq_map_answerTape (R : Type) [SampleableType R] (m : ℕ) :
    tapeList R m = List.ofFn <$> answerTape R m := by
  rw [tapeList]

@[simp] theorem tapeList_zero : tapeList R 0 = pure [] := by
  simp [tapeList]

theorem tapeList_succ (m : ℕ) :
    tapeList R (m + 1) =
      (do let u ← ($ᵗ R : ProbComp R)
          let l ← tapeList R m
          return u :: l) := by
  simp only [tapeList, answerTape_succ, map_bind, map_pure, bind_map_left]
  refine bind_congr fun u => ?_
  refine bind_congr fun w => ?_
  simp [List.ofFn_succ]

end TapeDraw

/-! ## Independent blocks and causal selected counts

`blockRunOf` samples an arbitrary left block and an independent right IID block, retaining both
complete blocks beside the entire run result.
A cell-selection event whose probability is unchanged by overwriting that cell can be charged
at a supplied fresh-hit rate. Summing the per-cell selections bounds the union by the expected
full selected count, without imposing a deterministic cap on that count.
-/

/-- Repeated independent runs of a fixed draw, collected as a list. -/
noncomputable def iidTapeList {B : Type} (rightDraw : ProbComp B) (length : Nat) :
    ProbComp (List B) :=
  List.ofFn <$> ProbComp.sampleIID length rightDraw

/-- Zero independent draws form the empty list. -/
theorem iidTapeList_zero {B : Type} (rightDraw : ProbComp B) :
    iidTapeList rightDraw 0 = pure [] := by
  simp [iidTapeList, ProbComp.sampleIID, Fin.mOfFn]

/-- A successor IID tape consists of one draw followed by the remaining draws. -/
theorem iidTapeList_succ {B : Type} (rightDraw : ProbComp B) (length : Nat) :
    iidTapeList rightDraw (length + 1) =
      (do let value ← rightDraw
          let rest ← iidTapeList rightDraw length
          return value :: rest) := by
  have step : ProbComp.sampleIID (length + 1) rightDraw =
      (do let value ← rightDraw
          let rest ← ProbComp.sampleIID length rightDraw
          return (Fin.cons value rest : Fin (length + 1) → B)) := by
    simp [ProbComp.sampleIID, Fin.mOfFn]
  simp only [iidTapeList, step, map_bind, map_pure, bind_map_left]
  refine bind_congr fun value => ?_
  refine bind_congr fun rest => ?_
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- One independent left block and a right IID tape, retained beside the complete run result. -/
@[expose] noncomputable def blockRunOf {A B ρ : Type}
    (leftBlock : ProbComp (List A)) (rightDraw : ProbComp B)
    (run : List A → List B → ProbComp ρ) (rightLength : Nat) :
    ProbComp ((List A × List B) × ρ) := do
  let leftTape ← leftBlock
  let rightTape ← iidTapeList rightDraw rightLength
  (fun result => ((leftTape, rightTape), result)) <$> run leftTape rightTape

/-- Supported blocked results are supported runs at their own supported sampled blocks. -/
theorem mem_support_blockRunOf {A B ρ : Type}
    (leftBlock : ProbComp (List A)) (rightDraw : ProbComp B)
    (run : List A → List B → ProbComp ρ) (rightLength : Nat)
    (outcome : (List A × List B) × ρ)
    (hmem : outcome ∈ support (blockRunOf leftBlock rightDraw run rightLength)) :
    outcome.1.1 ∈ support leftBlock ∧
      outcome.1.2 ∈ support (iidTapeList rightDraw rightLength) ∧
        outcome.2 ∈ support (run outcome.1.1 outcome.1.2) := by
  rw [blockRunOf, mem_support_bind_iff] at hmem
  obtain ⟨leftTape, hleftTape, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨rightTape, hrightTape, hinner⟩ := hrest
  rw [support_map] at hinner
  obtain ⟨result, hresult, hshape⟩ := hinner
  rw [← hshape]
  exact ⟨hleftTape, hrightTape, hresult⟩

/-- Redrawing one cell from its fixed law preserves the right IID tape's distribution. -/
theorem evalDist_iidTapeList_set {B γ : Type} (rightDraw : ProbComp B) :
    ∀ (length index : Nat), index < length →
      ∀ (continuation : List B → ProbComp γ),
        iidTapeList rightDraw length >>= continuation =ᵈ
          (iidTapeList rightDraw length >>= fun tape =>
            rightDraw >>= fun value => continuation (tape.set index value)) := by
  intro length
  induction length with
  | zero => intro index hindex; exact absurd hindex (by omega)
  | succ remaining ih =>
    intro index hindex continuation
    cases index with
    | zero =>
      simp only [iidTapeList_succ, bind_assoc, pure_bind, List.set_cons_zero]
      refine (OracleComp.EvalDistEq.bind_bind_swap _ (iidTapeList rightDraw remaining)
        fun value rest => continuation (value :: rest)).trans ?_
      exact (OracleComp.EvalDistEq.bind_const rightDraw _).symm
    | succ smaller =>
      simp only [iidTapeList_succ, bind_assoc, pure_bind, List.set_cons_succ]
      refine EvalDistEq.bind_right _ fun head => ?_
      exact ih smaller (by omega) fun rest => continuation (head :: rest)

/-- Uniform IID draws agree exactly with the canonical uniform answer tape program. -/
theorem iidTapeList_uniform_eq_tapeList {B : Type} [SampleableType B] (length : Nat) :
    iidTapeList ($ᵗ B : ProbComp B) length = tapeList B length := by
  induction length with
  | zero => rw [iidTapeList_zero, tapeList_zero]
  | succ length ih => rw [iidTapeList_succ, tapeList_succ, ih]

/-- A cell read back after it was overwritten is the value it was overwritten with. -/
private theorem eq_of_getElem?_set {B : Type} (tape : List B) (index : Nat) (value other : B)
    (hread : (tape.set index value)[index]? = some other) : other = value := by
  by_cases hlt : index < tape.length
  · rw [List.getElem?_set_self (by simpa using hlt)] at hread
    exact (Option.some_inj.mp hread).symm
  · rw [List.getElem?_eq_none (by simpa using Nat.not_lt.mp hlt)] at hread
    exact absurd hread (by simp)

open scoped Classical in
/-- A constant conjunct factors out of an event. -/
private theorem prEvent_const_and {γ : Type} (run : ProbComp γ) (constant : Prop)
    (event : γ → Prop) :
    Pr{let value ← run}[constant ∧ event value] =
      if constant then Pr{let x ← run}[event x] else 0 := by
  classical
  by_cases hconstant : constant
  · rw [ite_eq_left hconstant]
    exact prEvent_congr run _ _ fun _ => ⟨fun h => h.2, fun h => ⟨hconstant, h⟩⟩
  · rw [ite_eq_right hconstant]
    exact prEvent_eq_zero_of_forall_not run _ fun _ h => hconstant h.1

/-- A finite sum and a `tsum` over `ℝ≥0∞` may be exchanged. -/
private theorem sum_tsum_comm {Index Result : Type} (indices : Finset Index)
    (summand : Index → Result → ℝ≥0∞) :
    ∑ index ∈ indices, ∑' result : Result, summand index result =
      ∑' result : Result, ∑ index ∈ indices, summand index result := by
  classical
  refine Finset.induction_on indices ?_ ?_
  · simp
  · intro head rest hhead ih
    rw [Finset.sum_insert hhead, ih, ← ENNReal.tsum_add]
    refine tsum_congr fun result => ?_
    rw [Finset.sum_insert hhead]

open scoped Classical in
/-- A causal selected count charges one target cell at its fresh-hit rate. -/
theorem prob_selected_hit_le_of_causal {A B ρ : Type}
    (leftBlock : ProbComp (List A)) (rightDraw : ProbComp B)
    (run : List A → List B → ProbComp ρ)
    (len : ρ → Nat)
    (rightLength index : Nat) (hindex : index < rightLength)
    (goodBlock : List A → Prop) (hit : List A → B → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr{let value ← rightDraw}[hit leftTape value] ≤ rate)
    (hcausal : ∀ (leftTape : List A) (rightTape : List B) (value : B),
      Pr{let z ← run leftTape (rightTape.set index value)}[index < len z] =
        Pr{let z ← run leftTape rightTape}[index < len z]) :
    Pr{let outcome ← blockRunOf leftBlock rightDraw run rightLength}[
          index < len outcome.2 ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value] ≤
      Pr{let outcome ← blockRunOf leftBlock rightDraw run rightLength}[
          index < len outcome.2] * rate := by
  classical
  set target : List A → List B → ℝ≥0∞ := fun leftTape rightTape =>
    Pr{let result ← run leftTape rightTape}[index < len result] with htarget
  -- The selection alone, with the blocks forgotten.
  have hright : Pr{let outcome ← blockRunOf leftBlock rightDraw run rightLength}[
        index < len outcome.2] =
      ∑' leftTape, Pr{let x ← leftBlock}[x = leftTape] *
        ∑' rightTape, Pr{let x ← iidTapeList rightDraw rightLength}[x = rightTape] *
          target leftTape rightTape := by
    rw [blockRunOf, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun leftTape => congrArg _ ?_
    rw [OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun rightTape => congrArg _ ?_
    rw [prEvent_map]
  -- The charged event, after one cell of the target block is redrawn.
  have hleft : Pr{let outcome ← blockRunOf leftBlock rightDraw run rightLength}[
        index < len outcome.2 ∧ goodBlock outcome.1.1 ∧
          ∃ value, outcome.1.2[index]? = some value ∧ hit outcome.1.1 value] =
      ∑' leftTape, Pr{let x ← leftBlock}[x = leftTape] *
        ∑' rightTape, Pr{let x ← iidTapeList rightDraw rightLength}[x = rightTape] *
          ∑' value, Pr{let x ← rightDraw}[x = value] *
            Pr{let result ← run leftTape (rightTape.set index value)}[
                index < len result ∧ goodBlock leftTape ∧
                  ∃ other, (rightTape.set index value)[index]? = some other ∧
                    hit leftTape other] := by
    rw [blockRunOf]
    refine ((EvalDistEq.bind_right leftBlock fun leftTape =>
      evalDist_iidTapeList_set rightDraw rightLength index hindex
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
  calc ∑' value, Pr{let x ← rightDraw}[x = value] *
        Pr{let result ← run leftTape (rightTape.set index value)}[
            index < len result ∧ goodBlock leftTape ∧
              ∃ other, (rightTape.set index value)[index]? = some other ∧ hit leftTape other]
      ≤ ∑' value, Pr{let x ← rightDraw}[x = value] *
          (if goodBlock leftTape ∧ hit leftTape value then target leftTape rightTape else 0) := by
        refine ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl ?_
        refine le_trans (prEvent_mono _ _ (fun result : ρ =>
          (goodBlock leftTape ∧ hit leftTape value) ∧
            index < len result) ?_) ?_
        · rintro result ⟨hselected, hgood, other, hread, hhit⟩
          exact ⟨⟨hgood, (eq_of_getElem?_set rightTape index value other hread) ▸ hhit⟩,
            hselected⟩
        · rw [prEvent_const_and]
          by_cases hcase : goodBlock leftTape ∧ hit leftTape value
          · rw [ite_eq_left hcase, ite_eq_left hcase, htarget]
            exact le_of_eq (hcausal leftTape rightTape value)
          · rw [ite_eq_right hcase, ite_eq_right hcase]
    _ ≤ target leftTape rightTape * rate := by
        by_cases hgood : goodBlock leftTape
        · simp only [hgood, true_and]
          calc ∑' value, Pr{let x ← rightDraw}[x = value] *
                (if hit leftTape value then target leftTape rightTape else 0)
              = (∑' value, if hit leftTape value then
                  Pr{let x ← rightDraw}[x = value] else 0) *
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

/-- The sum of per-cell selection probabilities is bounded by the expected count. -/
theorem sum_prob_selected_le_expected_of {A B ρ : Type}
    (leftBlock : ProbComp (List A)) (rightDraw : ProbComp B)
    (run : List A → List B → ProbComp ρ)
    (len : ρ → Nat)
    (rightLength : Nat) :
    (∑ index : Fin rightLength,
        Pr{let outcome ← blockRunOf leftBlock rightDraw run rightLength}[
          index.val < len outcome.2]) ≤
      ∑' outcome, Pr{let x ← blockRunOf leftBlock rightDraw run rightLength}[x = outcome] *
        ((len outcome.2 : Nat) : ℝ≥0∞) := by
  classical
  calc ∑ index : Fin rightLength,
        Pr{let outcome ← blockRunOf leftBlock rightDraw run rightLength}[
          index.val < len outcome.2]
      = ∑ index : Fin rightLength, ∑' outcome,
          (if index.val < len outcome.2 then
            Pr{let x ← blockRunOf leftBlock rightDraw run rightLength}[x = outcome]
          else 0) :=
        Finset.sum_congr rfl fun index _ => OracleComp.prEvent_eq_tsum_ite _ _
    _ = ∑' outcome, ∑ index : Fin rightLength,
          (if index.val < len outcome.2 then
            Pr{let x ← blockRunOf leftBlock rightDraw run rightLength}[x = outcome]
          else 0) := sum_tsum_comm Finset.univ _
    _ ≤ ∑' outcome, Pr{let x ← blockRunOf leftBlock rightDraw run rightLength}[x = outcome] *
          ((len outcome.2 : Nat) : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun outcome => ?_
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
          mul_comm]
        refine mul_le_mul' le_rfl (Nat.cast_le.mpr ?_)
        have hinject := Finset.card_le_card_of_injOn (fun index : Fin rightLength => index.val)
          (s := Finset.univ.filter
            (fun index : Fin rightLength => index.val < len outcome.2))
          (t := Finset.range (len outcome.2))
          (fun index hindex => Finset.mem_range.mpr (by simpa using hindex))
          (fun left _ right _ hvalue => Fin.val_injective hvalue)
        simpa using hinject

open scoped Classical in
/-- The union of selected target hits is bounded by the expected count times the fresh-hit rate. -/
theorem prob_exists_hit_le_expected_of_causal {A B ρ : Type}
    (leftBlock : ProbComp (List A)) (rightDraw : ProbComp B)
    (run : List A → List B → ProbComp ρ)
    (len : ρ → Nat)
    (rightLength : Nat)
    (goodBlock : List A → Prop) (hit : List A → B → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ leftTape, goodBlock leftTape →
      Pr{let value ← rightDraw}[hit leftTape value] ≤ rate)
    (hcausal : ∀ (index : Nat) (leftTape : List A) (rightTape : List B)
        (value : B),
      Pr{let z ← run leftTape (rightTape.set index value)}[index < len z] =
        Pr{let z ← run leftTape rightTape}[index < len z]) :
    Pr{let outcome ← blockRunOf leftBlock rightDraw run rightLength}[
            ∃ index : Fin rightLength, index.val < len outcome.2 ∧
            goodBlock outcome.1.1 ∧
            ∃ value, outcome.1.2[index.val]? = some value ∧ hit outcome.1.1 value] ≤
      (∑' outcome, Pr{let x ← blockRunOf leftBlock rightDraw run rightLength}[x = outcome] *
        ((len outcome.2 : Nat) : ℝ≥0∞)) * rate := by
  classical
  refine le_trans (prEvent_mono _ _ (fun outcome => ∃ index ∈ (Finset.univ :
      Finset (Fin rightLength)), index.val < len outcome.2 ∧
      goodBlock outcome.1.1 ∧
      ∃ value, outcome.1.2[index.val]? = some value ∧ hit outcome.1.1 value)
    fun outcome hhit => by
      obtain ⟨index, hindex⟩ := hhit
      exact ⟨index, Finset.mem_univ index, hindex⟩) ?_
  refine le_trans (prEvent_exists_finset_le _ _ _) ?_
  refine le_trans (Finset.sum_le_sum fun index _ =>
    prob_selected_hit_le_of_causal leftBlock rightDraw run len rightLength
      index.val
      index.isLt goodBlock hit rate hrate (hcausal index.val)) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul' (sum_prob_selected_le_expected_of leftBlock rightDraw run len
    rightLength) le_rfl

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-! ## The tape-consuming lazy oracle -/

/-- The lazy random oracle with its fresh answers taken in order from a supplied list, sampling
uniformly once the list is exhausted. Its state is the answer cache together with the
unconsumed tape. -/
def tapeCachingImpl (D R : Type) [DecidableEq D] [SampleableType R] :
    QueryImpl (D →ₒ R) (StateT ((D →ₒ R).QueryCache × List R) ProbComp) :=
  fun t => StateT.mk fun s =>
    match s.1 t with
    | some u => pure (u, s)
    | none => match s.2 with
        | u :: l => pure (u, (s.1.cacheQuery t u, l))
        | [] => (fun u => (u, (s.1.cacheQuery t u, []))) <$> ($ᵗ R : ProbComp R)

theorem tapeCachingImpl_run_some {t : D} {c : (D →ₒ R).QueryCache} {l : List R} {u : R}
    (h : c t = some u) :
    ((tapeCachingImpl D R) t).run (c, l) = pure (u, (c, l)) := by
  simp [tapeCachingImpl, h]

theorem tapeCachingImpl_run_cons {t : D} {c : (D →ₒ R).QueryCache} {u : R} {l : List R}
    (h : c t = none) :
    ((tapeCachingImpl D R) t).run (c, u :: l) = pure (u, (c.cacheQuery t u, l)) := by
  simp [tapeCachingImpl, h]

theorem tapeCachingImpl_run_nil {t : D} {c : (D →ₒ R).QueryCache} (h : c t = none) :
    ((tapeCachingImpl D R) t).run (c, []) =
      (fun u => (u, (c.cacheQuery t u, ([] : List R)))) <$> ($ᵗ R : ProbComp R) := by
  simp [tapeCachingImpl, h]

/-! ## The identification -/

/-- **The lazy random oracle is the tape-consuming oracle averaged over an iid tape.** For every
tape length `m`, running `oa` under the lazy random oracle from cache `c` has the same joint
distribution of output and final cache as drawing `m` independent uniform answers, running `oa`
under `tapeCachingImpl` from `c` with that tape, and forgetting the unconsumed tape. -/
theorem evalDist_run_randomOracle_eq_tapeList {α : Type}
    (oa : OracleComp (D →ₒ R) α) (c : (D →ₒ R).QueryCache) (m : ℕ) :
    letI : MeasurableSpace (α × (D →ₒ R).QueryCache) := ⊤
    𝒟[(simulateQ (OracleSpec.randomOracle (spec := (D →ₒ R))) oa).run c] =
      𝒟[(do let l ← tapeList R m
            let z ← (simulateQ (tapeCachingImpl D R) oa).run (c, l)
            return (z.1, z.2.1))] := by
  let _ : MeasurableSpace (α × (D →ₒ R).QueryCache) := ⊤
  let _ : MeasurableSpace R := ⊤
  let _ : MeasurableSpace (List R) := ⊤
  induction oa using OracleComp.inductionOn generalizing c m with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    rw [_root_.evalDist_bind_const]
    rw [measure_univ, one_smul]
  | query_bind t k ih =>
    have hredL : (simulateQ (OracleSpec.randomOracle (spec := (D →ₒ R)))
          (liftM ((D →ₒ R).query t) >>= k)).run c =
        ((OracleSpec.randomOracle (spec := (D →ₒ R)) t).run c) >>= fun p =>
          (simulateQ OracleSpec.randomOracle (k p.1)).run p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hredR : ∀ l : List R,
        (simulateQ (tapeCachingImpl D R) (liftM ((D →ₒ R).query t) >>= k)).run (c, l) =
          (((tapeCachingImpl D R) t).run (c, l)) >>= fun p =>
            (simulateQ (tapeCachingImpl D R) (k p.1)).run p.2 := fun l => by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [hredL]
    simp only [hredR]
    rcases hc : c t with _ | u
    · rw [randomOracle.run_eq, hc]
      cases m with
      | zero =>
        simp only [tapeList_zero, pure_bind, tapeCachingImpl_run_nil hc, map_eq_bind_pure_comp,
          Function.comp_def, bind_assoc, pure_bind]
        rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
        apply Measure.bind_congr_right
        filter_upwards [] with u
        simpa only [tapeList_zero, pure_bind] using ih u (c.cacheQuery t u) 0
      | succ m' =>
        simp only [tapeList_succ, bind_assoc, pure_bind, tapeCachingImpl_run_cons hc]
        rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
        apply Measure.bind_congr_right
        filter_upwards [] with u
        exact ih u (c.cacheQuery t u) m'
    · rw [randomOracle.run_eq, hc, pure_bind]
      simp only [tapeCachingImpl_run_some hc, pure_bind]
      exact ih u c m

/-! ## The position instrumentation -/

/-- The position bookkeeping of one `tapeCachingImpl` step, as an auxiliary state
`(D → Option ℕ) × ℕ`: a query answered off the tape records the position it consumed and
advances the counter, while a cache hit and an answer sampled after the tape ran out record
nothing. -/
def positionAux (D R : Type) [DecidableEq D] :
    (t : D) → ((D →ₒ R).QueryCache × List R) → R → ((D →ₒ R).QueryCache × List R) →
      ((D → Option ℕ) × ℕ) → (D → Option ℕ) × ℕ :=
  fun t s _ _ p =>
    match s.1 t, s.2 with
    | none, _ :: _ => (Function.update p.1 t (some p.2), p.2 + 1)
    | _, _ => p

/-- The invariant maintained by the position instrumentation of a `tapeCachingImpl` run on the
tape `L`, relating the answer cache `c`, the unconsumed tape `l`, the position map `pm` and the
number `next` of tape entries consumed. -/
structure PositionInv (L : List R) (c : (D →ₒ R).QueryCache) (l : List R)
    (pm : D → Option ℕ) (next : ℕ) : Prop where
  /-- A recorded position has been consumed, and its cache entry is the tape value there. -/
  pos_spec : ∀ t n, pm t = some n → n < next ∧ c t = L[n]?
  /-- Distinct cached queries record distinct positions. -/
  pos_inj : ∀ t t' n, pm t = some n → pm t' = some n → t = t'
  /-- The consumed and unconsumed parts exhaust the tape. -/
  length_add : l.length + next = L.length
  /-- The unconsumed tape is the tail of `L` from the current position. -/
  getElem?_eq : ∀ i, l[i]? = L[next + i]?
  /-- No more positions have been consumed than there are cache entries. -/
  le_enncard : (next : ℝ≥0∞) ≤ c.enncard
  /-- A cache entry without a position was answered after the tape ran out. -/
  eq_nil_of_none : ∀ t, c t ≠ none → pm t = none → l = []
  /-- A cache entry without a position is one entry beyond the consumed positions. -/
  enncard_of_none : ∀ t, c t ≠ none → pm t = none → (next : ℝ≥0∞) + 1 ≤ c.enncard

namespace PositionInv

omit [DecidableEq D] [SampleableType R] in
/-- The empty cache with the full tape unconsumed satisfies the invariant. -/
theorem empty (L : List R) :
    PositionInv L (∅ : (D →ₒ R).QueryCache) L (fun _ => none) 0 where
  pos_spec _ _ h := absurd h (by simp)
  pos_inj _ _ _ h := absurd h (by simp)
  length_add := by simp
  getElem?_eq i := by simp
  le_enncard := by simp
  eq_nil_of_none t h := absurd (QueryCache.empty_apply t) h
  enncard_of_none t h := absurd (QueryCache.empty_apply t) h

end PositionInv

omit [SampleableType R] in
private theorem positionAux_of_some {t : D} {c : (D →ₒ R).QueryCache} {l : List R} {u : R}
    (h : c t = some u) (x : R) (s' : (D →ₒ R).QueryCache × List R) (p : (D → Option ℕ) × ℕ) :
    positionAux D R t (c, l) x s' p = p := by simp [positionAux, h]

omit [SampleableType R] in
private theorem positionAux_of_nil {t : D} {c : (D →ₒ R).QueryCache} (h : c t = none)
    (x : R) (s' : (D →ₒ R).QueryCache × List R) (p : (D → Option ℕ) × ℕ) :
    positionAux D R t (c, []) x s' p = p := by simp [positionAux, h]

omit [SampleableType R] in
private theorem positionAux_of_cons {t : D} {c : (D →ₒ R).QueryCache} {u : R} {l : List R}
    (h : c t = none) (x : R) (s' : (D →ₒ R).QueryCache × List R) (p : (D → Option ℕ) × ℕ) :
    positionAux D R t (c, u :: l) x s' p =
      (Function.update p.1 t (some p.2), p.2 + 1) := by simp [positionAux, h]

/-- Every step of the instrumented tape oracle preserves `PositionInv`. -/
private theorem positionInv_step (L : List R) (t : D)
    (s : ((D →ₒ R).QueryCache × List R) × (D → Option ℕ) × ℕ)
    (hs : PositionInv L s.1.1 s.1.2 s.2.1 s.2.2)
    (y : R × ((D →ₒ R).QueryCache × List R) × (D → Option ℕ) × ℕ)
    (hy : y ∈ support
      ((QueryImpl.extendState (tapeCachingImpl D R) (positionAux D R) t).run s)) :
    PositionInv L y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2 := by
  obtain ⟨⟨c, l⟩, pm, nx⟩ := s
  replace hs : PositionInv L c l pm nx := hs
  rw [QueryImpl.extendState_apply, mem_support_bind_iff] at hy
  obtain ⟨p, hp, hy⟩ := hy
  rw [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  rcases hc : c t with _ | u₀
  · rcases l with _ | ⟨u, l'⟩
    · rw [tapeCachingImpl_run_nil hc, support_map, support_uniformSample, Set.image_univ] at hp
      obtain ⟨u, hu⟩ := hp
      subst hu
      rw [positionAux_of_nil hc]
      change PositionInv L (c.cacheQuery t u) [] pm nx
      have hpmt : pm t = none := by
        rcases hpm : pm t with _ | n
        · rfl
        · obtain ⟨hlt, hval⟩ := hs.pos_spec t n hpm
          have hnx : nx = L.length := by simpa using hs.length_add
          rw [hc, List.getElem?_eq_getElem (by omega)] at hval
          exact absurd hval (by simp)
      have hen : (c.cacheQuery t u).enncard = c.enncard + 1 :=
        QueryCache.enncard_cacheQuery c t u hc
      refine ⟨fun t' n hn => ?_, hs.pos_inj, hs.length_add, hs.getElem?_eq, ?_,
        fun _ _ _ => rfl, fun _ _ _ => ?_⟩
      · have hne : t' ≠ t := fun h => by rw [h, hpmt] at hn; exact absurd hn (by simp)
        exact ⟨(hs.pos_spec t' n hn).1,
          (QueryCache.cacheQuery_of_ne c u hne).trans (hs.pos_spec t' n hn).2⟩
      · exact hen ▸ le_add_right hs.le_enncard
      · exact hen ▸ add_le_add hs.le_enncard le_rfl
    · rw [tapeCachingImpl_run_cons hc, support_pure, Set.mem_singleton_iff] at hp
      subst hp
      rw [positionAux_of_cons hc]
      change PositionInv L (c.cacheQuery t u) l' (Function.update pm t (some nx)) (nx + 1)
      have hen : (c.cacheQuery t u).enncard = c.enncard + 1 :=
        QueryCache.enncard_cacheQuery c t u hc
      have hu : c.cacheQuery t u t = L[nx]? := by
        rw [QueryCache.cacheQuery_self]
        simpa using hs.getElem?_eq 0
      have hvac : ∀ t', (c.cacheQuery t u) t' ≠ none →
          Function.update pm t (some nx) t' = none → False := by
        intro t' h₁ h₂
        rcases eq_or_ne t' t with rfl | hne
        · rw [Function.update_self] at h₂; exact absurd h₂ (by simp)
        · rw [Function.update_of_ne hne] at h₂
          rw [QueryCache.cacheQuery_of_ne c u hne] at h₁
          exact absurd (hs.eq_nil_of_none t' h₁ h₂) (by simp)
      refine ⟨fun t' n hn => ?_, fun t₁ t₂ n h₁ h₂ => ?_, ?_, fun i => ?_, ?_,
        fun t' h₁ h₂ => (hvac t' h₁ h₂).elim, fun t' h₁ h₂ => (hvac t' h₁ h₂).elim⟩
      · rcases eq_or_ne t' t with rfl | hne
        · rw [Function.update_self, Option.some_inj] at hn
          exact hn ▸ ⟨Nat.lt_succ_self _, hu⟩
        · rw [Function.update_of_ne hne] at hn
          exact ⟨(hs.pos_spec t' n hn).1.trans (Nat.lt_succ_self _),
            (QueryCache.cacheQuery_of_ne c u hne).trans (hs.pos_spec t' n hn).2⟩
      · rcases eq_or_ne t₁ t with rfl | hne₁
        · rcases eq_or_ne t₂ t₁ with rfl | hne₂
          · rfl
          · rw [Function.update_self, Option.some_inj] at h₁
            rw [Function.update_of_ne hne₂] at h₂
            exact absurd (hs.pos_spec t₂ n h₂).1 (by omega)
        · rw [Function.update_of_ne hne₁] at h₁
          rcases eq_or_ne t₂ t with rfl | hne₂
          · rw [Function.update_self, Option.some_inj] at h₂
            exact absurd (hs.pos_spec t₁ n h₁).1 (by omega)
          · rw [Function.update_of_ne hne₂] at h₂
            exact hs.pos_inj t₁ t₂ n h₁ h₂
      · have h := hs.length_add
        rw [List.length_cons] at h
        omega
      · have h := hs.getElem?_eq (i + 1)
        rw [List.getElem?_cons_succ] at h
        rw [h, show nx + (i + 1) = nx + 1 + i from by omega]
      · rw [hen, Nat.cast_add, Nat.cast_one]
        exact add_le_add hs.le_enncard le_rfl
  · rw [tapeCachingImpl_run_some hc, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rw [positionAux_of_some hc]
    exact hs

/-- **Every cache entry of a tape-consuming run sits at its own tape position.** In a run of
`oa` under `tapeCachingImpl` from the empty cache on the length-`q` tape `v`, if the final cache
has at most `q` entries then each of its entries is the tape value at a position of the tape,
and distinct cached queries have distinct positions.

The cache bound is what excludes the fallback answers sampled after the tape runs out: such an
answer requires the tape to be exhausted first, so the cache would already hold `q` entries. -/
theorem exists_pos_of_mem_support_run_tapeCachingImpl {α : Type} {q : ℕ} (v : Fin q → R)
    (oa : OracleComp (D →ₒ R) α) {z : α × (D →ₒ R).QueryCache × List R}
    (hz : z ∈ support ((simulateQ (tapeCachingImpl D R) oa).run (∅, List.ofFn v)))
    (hq : z.2.1.enncard ≤ (q : ℝ≥0∞)) :
    ∃ pos : D → Option (Fin q),
      (∀ t u, z.2.1 t = some u → ∃ i, pos t = some i ∧ u = v i) ∧
      (∀ t t' i, pos t = some i → pos t' = some i → t = t') := by
  classical
  have hlen : (List.ofFn v).length = q := List.length_ofFn
  rw [← extendState_run_proj_eq (tapeCachingImpl D R) (positionAux D R) oa
    (∅, List.ofFn v) ((fun _ => none), 0), support_map] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hinv := simulateQ_run_preserves_inv_of_query
    (QueryImpl.extendState (tapeCachingImpl D R) (positionAux D R))
    (fun s => PositionInv (List.ofFn v) s.1.1 s.1.2 s.2.1 s.2.2)
    (fun t s hs => positionInv_step (List.ofFn v) t s hs) oa _
    (PositionInv.empty (List.ofFn v)) y hy
  have hc : y.2.1.1 = z.2.1 := by rw [← hyz]; rfl
  rw [hc] at hinv
  have hsome : ∀ t, z.2.1 t ≠ none → ∃ n, y.2.2.1 t = some n := by
    intro t ht
    rcases hpm : y.2.2.1 t with _ | n
    · have hnx : y.2.2.2 = q := by
        have h := hinv.length_add
        rw [hinv.eq_nil_of_none t ht hpm, hlen] at h
        simpa using h
      have h₁ : ((y.2.2.2 : ℕ) : ℝ≥0∞) + 1 ≤ (q : ℝ≥0∞) :=
        (hinv.enncard_of_none t ht hpm).trans hq
      rw [hnx] at h₁
      exact absurd h₁
        (not_le.mpr (ENNReal.lt_add_right (ENNReal.natCast_ne_top q) one_ne_zero))
    · exact ⟨n, rfl⟩
  set pos : D → Option (Fin q) :=
    fun t => (y.2.2.1 t).bind fun n => if h : n < q then some ⟨n, h⟩ else none with hpos
  have hposval : ∀ t (i : Fin q), pos t = some i → y.2.2.1 t = some (i : ℕ) := by
    intro t i hi
    simp only [hpos] at hi
    obtain ⟨n, hn⟩ : ∃ n, y.2.2.1 t = some n :=
      Option.ne_none_iff_exists'.mp fun hnone => by
        rw [hnone] at hi; exact absurd hi (by simp)
    rw [hn] at hi ⊢
    replace hi : (if h : n < q then some (⟨n, h⟩ : Fin q) else none) = some i := hi
    by_cases hnq : n < q
    · rw [dite_eq_left hnq, Option.some_inj] at hi
      rw [← hi]
    · rw [dite_eq_right hnq] at hi
      exact absurd hi (by simp)
  refine ⟨pos, fun t u hu => ?_, fun t t' i h h' =>
    hinv.pos_inj t t' (i : ℕ) (hposval t i h) (hposval t' i h')⟩
  obtain ⟨n, hn⟩ := hsome t (by simp [hu])
  obtain ⟨hlt, hval⟩ := hinv.pos_spec t n hn
  have hnq : n < q := by have h := hinv.length_add; omega
  refine ⟨⟨n, hnq⟩, by simp [hpos, hn, hnq], ?_⟩
  rw [hu, List.getElem?_eq_getElem (by simpa using hnq)] at hval
  simpa using hval

/-! ## Transporting a tape bound -/

/-- **Transporting a tape bound to a lazy random-oracle run, as an event probability.** If the
tape event `E` has probability at most `b`, and off `E` no run of `oa` under `tapeCachingImpl`
on that tape can leave a final cache satisfying `P`, then the lazy random-oracle run leaves a
cache satisfying `P` with probability at most `b`. -/
theorem prEvent_run_randomOracle_le_of_transport {α : Type} (q : ℕ)
    (oa : OracleComp (D →ₒ R) α) (P : (D →ₒ R).QueryCache → Prop) (E : (Fin q → R) → Prop)
    (b : ℝ≥0∞) (hE : Pr{let v ← answerTape R q}[E v] ≤ b)
    (htransport : ∀ v : Fin q → R, ¬ E v →
      ∀ z ∈ support ((simulateQ (tapeCachingImpl D R) oa).run (∅, List.ofFn v)), ¬ P z.2.1) :
    Pr{let z ← (simulateQ (OracleSpec.randomOracle (spec := (D →ₒ R))) oa).run ∅}[P z.2] ≤
      b := by
  rw [(evalDistEq_iff_evalDist_eq.mpr (evalDist_run_randomOracle_eq_tapeList oa ∅ q)).prEvent_eq]
  refine le_trans (le_of_eq ?_) ((prEvent_bind_le_prEvent_of_forall_eq_zero (answerTape R q)
    (fun v => (simulateQ (tapeCachingImpl D R) oa).run (∅, List.ofFn v)) E (fun z => P z.2.1)
    fun v hv => ?_).trans hE)
  · simp only [tapeList_eq_map_answerTape, bind_map_left, prEvent_norm]
  · exact prEvent_eq_zero_of_forall_mem_support _ _ (htransport v hv)

variable [MeasurableSpace R] [DiscreteMeasurableSpace R]

/-- **Transporting a tape bound to a lazy random-oracle run.** If the tape event `E` has mass at
most `b`, and off `E` no run of `oa` under `tapeCachingImpl` on that tape can leave a final cache
satisfying `P`, then the lazy random-oracle run leaves a cache satisfying `P` with mass at most
`b`. -/
theorem evalDist_run_randomOracle_setOf_le_of_transport {α : Type} (q : ℕ)
    (oa : OracleComp (D →ₒ R) α) (P : (D →ₒ R).QueryCache → Prop) (E : Set (Fin q → R))
    (b : ℝ≥0∞) (hE : 𝒟[answerTape R q] E ≤ b)
    (htransport : ∀ v : Fin q → R, v ∉ E →
      ∀ z ∈ support ((simulateQ (tapeCachingImpl D R) oa).run (∅, List.ofFn v)), ¬ P z.2.1) :
    letI : MeasurableSpace (α × (D →ₒ R).QueryCache) := ⊤
    𝒟[(simulateQ (OracleSpec.randomOracle (spec := (D →ₒ R))) oa).run ∅] {z | P z.2} ≤ b := by
  classical
  let _ : MeasurableSpace (α × (D →ₒ R).QueryCache) := ⊤
  rw [evalDist_run_randomOracle_eq_tapeList oa ∅ q]
  refine le_trans ?_ hE
  simp only [tapeList, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine evalDist_bind_apply_le_of_forall_notMem_eq_zero _ _ MeasurableSet.of_discrete
    MeasurableSet.of_discrete fun v hv => ?_
  refine evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete fun z hz => ?_
  rw [mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact htransport v hv w hw

end AnswerTape
