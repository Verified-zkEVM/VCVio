/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.TapeFactor
public import HashSig.SLHDSA.SHAKE128s.Proof.Averaging

/-!
# A block of answers, read as a tape of parsed views

`TapeFactor` hands the coverage charge blocks of `List HashOutput`, drawn by `DigestTape.padding`,
and takes the hit relation as a parameter. The FORS machinery states everything about
`ForsDisclosureTape.Tape n = Fin n → View` instead. This file is the one conversion between the
two, and the hit relation `BlockHit` the game needs: a fresh answer whose fourteen FORS leaves are
all disclosed by the block.

`DigestTape.viewTape_uniform` already says a uniform *word* parses to a uniform tape. What is
missing is that `padding` draws a uniform word at all (it draws one answer at a time), and that is
`evalDist_padding_eq_ofFn`, by splitting a uniform function type at its first coordinate.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BlockViews

open DigestTape TapeFactor

/-! ## A block is a uniform word -/

/-- Uniform sampling of a pair is two independent draws. -/
theorem uniformSample_prod_eq_bind {α β : Type} [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do let left ← $ᵗ α; let right ← $ᵗ β; pure (left, right)) := by
  rw [uniformSample]
  change ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β)) = _
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]

/-- Consing one answer onto a word is a bijection from the pair. -/
theorem cons_bijective (length : Nat) :
    Function.Bijective (fun pair : HashOutput × (Fin length → HashOutput) =>
      Fin.cons pair.1 pair.2 : HashOutput × (Fin length → HashOutput) →
        Fin (length + 1) → HashOutput) := by
  constructor
  · intro left right hsame
    have hhead := congrFun hsame 0
    have htail : ∀ index : Fin length, left.2 index = right.2 index := fun index => by
      have := congrFun hsame index.succ
      simpa using this
    exact Prod.ext (by simpa using hhead) (funext htail)
  · intro word
    exact ⟨(word 0, Fin.tail word), Fin.cons_self_tail word⟩

/-- **A block of independent draws is a uniform word.** `padding` draws one answer at a time;
the FORS machinery wants a function off `Fin length`. They agree. -/
theorem evalDist_padding_eq_ofFn (length : Nat) :
    padding length =ᵈ
      (List.ofFn <$> ($ᵗ (Fin length → HashOutput) :
        ProbComp (Fin length → HashOutput))) := by
  induction length with
  | zero =>
    refine evalDistEq_iff_evalDist_eq.mpr ?_
    rw [padding, show (List.ofFn : (Fin 0 → HashOutput) → List HashOutput) =
        fun _ => ([] : List HashOutput) from by funext word; simp]
    simp
  | succ remaining ih =>
    have hbijection :=
      SampleableType.map_uniformSample_evalDistEq_of_bijective (cons_bijective remaining)
    calc padding (remaining + 1)
        = (($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
            padding remaining >>= fun rest => (pure (value :: rest) : ProbComp _)) := rfl
      _ =ᵈ (($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
            (List.ofFn <$> ($ᵗ (Fin remaining → HashOutput) : ProbComp _)) >>= fun rest =>
              (pure (value :: rest) : ProbComp _)) :=
          EvalDistEq.bind_right _ fun _ => ih.bind_left _
      _ = (fun pair : HashOutput × (Fin remaining → HashOutput) =>
              pair.1 :: List.ofFn pair.2) <$>
            ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _) := by
          rw [uniformSample_prod_eq_bind]
          simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      _ = List.ofFn <$> ((fun pair : HashOutput × (Fin remaining → HashOutput) =>
              (Fin.cons pair.1 pair.2 : Fin (remaining + 1) → HashOutput)) <$>
            ($ᵗ (HashOutput × (Fin remaining → HashOutput)) : ProbComp _)) := by
          rw [Functor.map_map]
          congr 1
          funext pair
          simp [List.ofFn_succ]
      _ =ᵈ List.ofFn <$> ($ᵗ (Fin (remaining + 1) → HashOutput) : ProbComp _) :=
          hbijection.map _

/-! ## The block as a tape -/

/-- **A fresh answer parses to a uniform view.** -/
theorem evalDist_parse_uniform :
    (MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ
      ($ᵗ MessageDigest.View : ProbComp MessageDigest.View) := by
  have hsplit :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective MessageDigest.split_bijective
  calc MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)
      = Prod.fst <$> (MessageDigest.split <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
        rw [Functor.map_map]
        rfl
    _ =ᵈ Prod.fst <$> ($ᵗ (MessageDigest.View × (BitVec 2 × BitVec 7)) : ProbComp _) :=
        hsplit.map _
    _ =ᵈ _ := EvalDistEq.of_forall_prEvent_eq fun p => by
        rw [prEvent_map]
        exact SampleableType.prEvent_uniformSample_fst p

/-- A block of answers, read as a tape of parsed FORS views. Cells past the block's end read as
a default, which never happens where the charge looks: it reads cell `index` only when the run
recorded an answer there. -/
def blockTape (length : Nat) (block : List HashOutput) : ForsDisclosureTape.Tape length :=
  fun index => MessageDigest.parse (block.getD index.val default)

/-- **A drawn block is a uniform tape.** -/
theorem evalDist_blockTape (length : Nat) :
    (blockTape length <$> padding length) =ᵈ
      ($ᵗ (ForsDisclosureTape.Tape length) :
        ProbComp (ForsDisclosureTape.Tape length)) := by
  calc blockTape length <$> padding length
      =ᵈ blockTape length <$>
          (List.ofFn <$> ($ᵗ (Fin length → HashOutput) : ProbComp _)) :=
        (evalDist_padding_eq_ofFn length).map _
    _ = (fun word index => MessageDigest.parse (word index)) <$>
          ($ᵗ (Fin length → HashOutput) : ProbComp _) := by
        rw [Functor.map_map]
        congr 1
        funext word
        funext index
        simp [blockTape, List.getD_eq_getElem?_getD]
    _ =ᵈ _ := viewTape_uniform length

/-! ## The hit relation the game needs -/

/-- An answer whose fourteen FORS leaves are all disclosed by the block. -/
def BlockHit (length : Nat) (block : List HashOutput) (value : HashOutput) : Prop :=
  ForsCoverage.Covered (ForsDisclosureTape.disclosures (blockTape length block))
    (MessageDigest.parse value)

variable {σ : Type} [RecorderView.CacheView σ]

/-- An integral against the output measure of a sampling computation is the sum of its singleton
masses times the integrand. -/
private theorem lintegral_evalDist_eq_tsum_probComp {β : Type} (run : ProbComp β)
    (weight : β → ℝ≥0∞) :
    letI : MeasurableSpace β := ⊤
    ∫⁻ value, weight value ∂𝒟[run] = ∑' value, Pr{let x ← run}[x = value] * weight value := by
  let : MeasurableSpace β := ⊤
  have hae : ∀ᵐ value ∂𝒟[run], value ∈ support run :=
    evalDist.ae_of_forall_mem_support run (· ∈ support run) MeasurableSet.of_discrete
      fun _ h ↦ h
  rw [← MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae,
    MeasureTheory.lintegral_countable weight (support_finite run).countable,
    ← tsum_subtype_eq_of_support_subset (s := support run)
      (f := fun value ↦ Pr{let x ← run}[x = value] * weight value)]
  · simp only [prEvent_eq_evalDist_singleton, mul_comm]
  · intro value hvalue
    by_contra hnot
    refine hvalue ?_
    simp only
    rw [prEvent_eq_evalDist_singleton,
      MeasureTheory.measure_mono_null (Set.singleton_subset_iff.2 hnot)
        (MeasureTheory.ae_iff.1 hae), zero_mul]

open scoped Classical in
/-- Expectations move through a reshaping of the outcome. -/
theorem tsum_probOutput_map {β γ : Type} [DecidableEq γ] (run : ProbComp β) (reshape : β → γ)
    (weight : γ → ℝ≥0∞) :
    ∑' value, Pr{let x ← reshape <$> run}[x = value] * weight value =
      ∑' value, Pr{let x ← run}[x = value] * weight (reshape value) := by
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace γ := ⊤
  rw [← lintegral_evalDist_eq_tsum_probComp, ← lintegral_evalDist_eq_tsum_probComp,
    lintegral_evalDist_map_of_discrete]

end SlhDsaSecurity.BlockViews
