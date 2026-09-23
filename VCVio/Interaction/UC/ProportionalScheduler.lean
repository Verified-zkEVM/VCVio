/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import PolyFun.Interaction.UC.OpenProcessQuotient
public import PolyFun.Interaction.UC.ScheduledSamplerFactorization
public import PolyFun.Interaction.UC.ScheduledOpenProcessModel
public import VCVio.EvalDist.Fintype
public import VCVio.EvalDist.Monad.Map
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-!
# Proportional UC scheduling

This module instantiates PolyFun's mass-aware binary scheduler in `ProbComp`.
A binary node draws uniformly from all slots in its two subtrees and selects
the subtree containing the drawn slot. Thus a leaf with mass `w` is selected
with probability `w` divided by the total mass, independently of how the
composition tree is parenthesized.

The coherence law is deliberately denotational: two scheduler computations
are related when they have the same output distribution. The underlying oracle
programs may issue differently shaped uniform queries after reassociation, but
the induced observable distributions agree.

The relation is also a congruence for the continuation of `bind`
(`outputRel_isBindCongr`), so sampler equivalence at `outputRel` is a
congruence on `theory Party`. The quotient `quotientTheory Party` satisfies
plug factorization (`hasPlugFactorization_quotientTheory`).
-/

public section

universe u

namespace Interaction
namespace UC

open OpenProcessFactorization OracleComp

namespace ProportionalScheduler

/-! ## Denotational relation -/

/-- Equality of output distributions of `ProbComp` computations, compared as measures on the
discrete measurable structure of the output type. This is the denotational equality used for
scheduler coherence; `outputRel_rel` reads it as pointwise equality of output probabilities. -/
noncomputable def outputRel : MonadRelFamily ProbComp where
  rel := fun {α} left right => letI : MeasurableSpace α := ⊤; 𝒟[left] = 𝒟[right]
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂
  map_congr := by
    intro α β f left right h
    let : MeasurableSpace α := ⊤
    let : MeasurableSpace β := ⊤
    change 𝒟[f <$> left] = 𝒟[f <$> right]
    rw [evalDist_map left Measurable.of_discrete, evalDist_map right Measurable.of_discrete]
    exact congrArg (MeasureTheory.Measure.map f) h
  bind_congr := by
    intro α β left right f h
    let : MeasurableSpace α := ⊤
    let : MeasurableSpace β := ⊤
    change 𝒟[left >>= f] = 𝒟[right >>= f]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    exact congrArg (MeasureTheory.Measure.bind · fun x => 𝒟[f x]) h

/-- `outputRel` holds exactly when the output probabilities agree pointwise. -/
@[simp]
theorem outputRel_rel {α : Type} (left right : ProbComp α) :
    outputRel.rel left right ↔
      ∀ output, Pr[= output | left] = Pr[= output | right] := by
  let : MeasurableSpace α := ⊤
  change 𝒟[left] = 𝒟[right] ↔ _
  rw [← evalSPMF_ext_iff]
  exact ⟨evalSPMF_eq_of_evalDist_eq left right, evalDist_eq_of_evalSPMF_eq left right⟩

/-- `outputRel` is a congruence for the continuation of `bind`: the output distribution of
`x >>= f` is the Giry bind of the output distribution of `x` against those of `f`. -/
instance outputRel_isBindCongr : outputRel.IsBindCongr where
  bind_congr_right := by
    intro α β x f g h
    let : MeasurableSpace α := ⊤
    let : MeasurableSpace β := ⊤
    change 𝒟[x >>= f] = 𝒟[x >>= g]
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
    exact congrArg (MeasureTheory.Measure.bind 𝒟[x]) (funext h)

/-- A finite sum over lifted Booleans has exactly its two expected terms. -/
theorem sum_ulift_bool (f : ULift Bool → ENNReal) :
    ∑ choice, f choice = f (ULift.up false) + f (ULift.up true) := by
  have univ_eq : (Finset.univ : Finset (ULift Bool)) =
      {ULift.up false, ULift.up true} := by
    ext choice
    obtain ⟨choice⟩ := choice
    cases choice <;> simp
  rw [univ_eq]
  simp

/-! ## Uniform slot draws -/

/-- A uniform draw from the positive set of slots represented by `mass`. -/
noncomputable def drawSlot (mass : ℕ+) : ProbComp (Fin mass.val) :=
  letI : Nonempty (Fin mass.val) := ⟨⟨0, mass.pos⟩⟩
  letI := SampleableType.ofFintype (Fin mass.val)
  $ᵗ (Fin mass.val)

/-- The number of indices below `cut` inside `Fin total` is `cut`. -/
theorem card_filter_fin_lt (cut total : Nat) (hcut : cut ≤ total) :
    ((Finset.univ : Finset (Fin total)).filter fun index => index.val < cut).card = cut := by
  let e : {index : Fin total // index.val < cut} ≃ Fin cut :=
    { toFun := fun index => ⟨index.val.val, index.property⟩
      invFun := fun index =>
        ⟨⟨index.val, lt_of_lt_of_le index.isLt hcut⟩, index.isLt⟩
      left_inv := fun index => by ext; rfl
      right_inv := fun index => by ext; rfl }
  rw [← Fintype.card_subtype]
  simpa using Fintype.card_congr e

/-- The number of indices in the half-open interval `[lower, upper)` inside
`Fin total` is `upper - lower`. -/
theorem card_filter_fin_Ico (lower upper total : Nat)
    (hlower : lower ≤ upper) (hupper : upper ≤ total) :
    ((Finset.univ : Finset (Fin total)).filter fun index =>
      lower ≤ index.val ∧ index.val < upper).card = upper - lower := by
  let e : {index : Fin total // lower ≤ index.val ∧ index.val < upper} ≃
      Fin (upper - lower) :=
    { toFun := fun index => ⟨index.val.val - lower, by omega⟩
      invFun := fun index => by
        have hindex := index.isLt
        have hltUpper : lower + index.val < upper := by omega
        exact ⟨⟨lower + index.val, lt_of_lt_of_le hltUpper hupper⟩,
          Nat.le_add_right lower index.val, hltUpper⟩
      left_inv := fun index => by
        apply Subtype.ext
        apply Fin.ext
        simp only
        exact Nat.add_sub_of_le index.property.1
      right_inv := fun index => by
        apply Fin.ext
        simp }
  rw [← Fintype.card_subtype]
  simpa using Fintype.card_congr e

/-- A uniform slot draw gives any decidable event its relative cardinality. -/
theorem probEvent_drawSlot (mass : ℕ+) (p : Fin mass.val → Prop)
    [DecidablePred p] :
    Pr[ p | drawSlot mass] =
      ((Finset.univ.filter p).card : ENNReal) / mass.val := by
  simp [drawSlot, probEvent_uniformSample, Fintype.card_fin]

/-! ## Binary and flat schedulers -/

/-- Select the left subtree exactly when the uniformly drawn slot lies in the
left subtree's initial segment. -/
noncomputable def binary : BinaryScheduler ProbComp :=
  fun left right =>
    (fun slot => ULift.up (decide (slot.val < left.val))) <$> drawSlot (left + right)

/-- Point probability of proportional binary scheduling. -/
theorem probOutput_binary (left right : ℕ+) (choice : ULift Bool) :
    Pr[= choice | binary left right] =
      if choice.down then
        (left.val : ENNReal) / (left.val + right.val)
      else
        (right.val : ENNReal) / (left.val + right.val) := by
  rw [binary, probOutput_map]
  obtain ⟨choice⟩ := choice
  cases choice
  · rw [probEvent_drawSlot]
    simp only [Bool.false_eq]
    have hevent :
        ((Finset.univ : Finset (Fin (left + right).val)).filter
          fun index => ULift.up (decide (index.val < left.val)) = ULift.up false) =
        (Finset.univ.filter fun index => ¬index.val < left.val) := by
      ext index
      simp
    rw [hevent]
    have hcard :
        ((Finset.univ : Finset (Fin (left + right).val)).filter
          fun index => ¬index.val < left.val).card = right.val := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin (left + right).val)))
        (fun index => index.val < left.val)
      rw [Finset.card_univ, Fintype.card_fin,
        card_filter_fin_lt left.val (left + right).val (by simp)] at hpartition
      simpa using hpartition
    rw [hcard]
    simp
  · rw [probEvent_drawSlot]
    have hevent :
        ((Finset.univ : Finset (Fin (left + right).val)).filter
          fun index => ULift.up (decide (index.val < left.val)) = ULift.up true) =
        (Finset.univ.filter fun index => index.val < left.val) := by
      ext index
      simp
    rw [hevent]
    rw [card_filter_fin_lt left.val (left + right).val (by simp)]
    simp

/-- Classify a slot in a three-way frontier. -/
def classifyThree (first second : ℕ+) {total : Nat}
    (slot : Fin total) : ULift Leaf :=
  if slot.val < first.val then
    ULift.up .first
  else if slot.val < first.val + second.val then
    ULift.up .second
  else
    ULift.up .context

/-- Direct parenthesization-free draw from three component frontiers. -/
noncomputable def flat : BinaryScheduler.FlatChoice ProbComp :=
  fun first second context =>
    classifyThree first second <$> drawSlot (first + second + context)

/-- Point probability of the direct three-way scheduler. -/
theorem probOutput_flat (first second context : ℕ+) (leaf : ULift Leaf) :
    Pr[= leaf | flat first second context] =
      match leaf.down with
      | .first => (first.val : ENNReal) /
          (first.val + second.val + context.val)
      | .second => (second.val : ENNReal) /
          (first.val + second.val + context.val)
      | .context => (context.val : ENNReal) /
          (first.val + second.val + context.val) := by
  rw [flat, probOutput_map]
  obtain ⟨leaf⟩ := leaf
  cases leaf
  all_goals rw [probEvent_drawSlot]
  · have hevent :
        ((Finset.univ : Finset (Fin (first + second + context).val)).filter
          fun slot => classifyThree first second slot = ULift.up Leaf.first) =
        (Finset.univ.filter fun slot => slot.val < first.val) := by
      ext slot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold classifyThree
      split_ifs <;> simp_all
    rw [hevent, card_filter_fin_lt first.val (first + second + context).val
      (by simp only [PNat.add_coe]; omega)]
    simp
  · have hevent :
        ((Finset.univ : Finset (Fin (first + second + context).val)).filter
          fun slot => classifyThree first second slot = ULift.up Leaf.second) =
        (Finset.univ.filter fun slot =>
          first.val ≤ slot.val ∧ slot.val < first.val + second.val) := by
      ext slot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold classifyThree
      split_ifs <;> simp_all
    rw [hevent, card_filter_fin_Ico first.val (first.val + second.val)
      (first + second + context).val (by omega)
        (by simp only [PNat.add_coe]; omega)]
    simp
  · have hevent :
        ((Finset.univ : Finset (Fin (first + second + context).val)).filter
          fun slot => classifyThree first second slot = ULift.up Leaf.context) =
        (Finset.univ.filter fun slot =>
          ¬slot.val < first.val + second.val) := by
      ext slot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold classifyThree
      split_ifs <;> simp_all
      omega
    rw [hevent]
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (first + second + context).val)))
      (fun slot => slot.val < first.val + second.val)
    rw [Finset.card_univ, Fintype.card_fin,
      card_filter_fin_lt (first.val + second.val)
        (first + second + context).val
        (by simp only [PNat.add_coe]; omega)] at hpartition
    simp only [PNat.add_coe] at hpartition
    have hcard :
        ((Finset.univ : Finset (Fin (first + second + context).val)).filter
          fun slot => ¬slot.val < first.val + second.val).card = context.val := by
      exact Nat.add_left_cancel hpartition
    rw [hcard]
    simp

/-- Multiplying a component's conditional share by its combined frontier's
outer share cancels the intermediate mass. -/
theorem nested_ratio (selected combined context : Nat) (hcombined : 0 < combined) :
    (combined : ENNReal) / (combined + context) *
        ((selected : ENNReal) / combined) =
      (selected : ENNReal) / (combined + context) := by
  have hzero : (combined : ENNReal) ≠ 0 := by
    simp [Nat.ne_of_gt hcombined]
  have htop : (combined : ENNReal) ≠ ⊤ := by simp
  rw [mul_comm, ← mul_div_assoc, ENNReal.div_mul_cancel hzero htop]

/-! ## Coherence -/

/-- Proportional scheduling factors every hierarchical three-way draw through
the same direct distribution. -/
theorem isFlat : BinaryScheduler.IsFlat outputRel binary flat := by
  constructor
  · intro left right
    rw [outputRel_rel]
    intro choice
    rw [probOutput_binary, probOutput_map]
    obtain ⟨choice⟩ := choice
    cases choice
    all_goals simp [BinaryScheduler.flip, probOutput_binary,
      probEvent_eq_tsum_indicator, sum_ulift_bool, add_comm]
  · intro first second context
    rw [outputRel_rel]
    intro leaf
    obtain ⟨leaf⟩ := leaf
    cases leaf
    all_goals simp [BinaryScheduler.sourceDraw, probOutput_bind_eq_sum_fintype,
      sum_ulift_bool, probOutput_binary, probOutput_flat, probOutput_pure]
    · simpa only [Nat.cast_add] using
        nested_ratio first.val (first.val + second.val) context.val
          (Nat.add_pos_left first.pos _)
    · simpa only [Nat.cast_add] using
        nested_ratio second.val (first.val + second.val) context.val
          (Nat.add_pos_left first.pos _)
  · intro first second context
    rw [outputRel_rel]
    intro leaf
    obtain ⟨leaf⟩ := leaf
    cases leaf
    all_goals simp [BinaryScheduler.leftDraw, probOutput_bind_eq_sum_fintype,
      sum_ulift_bool, probOutput_binary, probOutput_flat, probOutput_pure,
      add_comm, add_assoc]
    · simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        nested_ratio second.val (context.val + second.val) first.val
          (Nat.add_pos_left context.pos _)
    · simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        nested_ratio context.val (context.val + second.val) first.val
          (Nat.add_pos_left context.pos _)
  · intro first second context
    rw [outputRel_rel]
    intro leaf
    obtain ⟨leaf⟩ := leaf
    cases leaf
    all_goals simp [BinaryScheduler.rightDraw, probOutput_bind_eq_sum_fintype,
      sum_ulift_bool, probOutput_binary, probOutput_flat, probOutput_pure,
      add_comm, add_left_comm, add_assoc]
    · simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        nested_ratio first.val (context.val + first.val) second.val
          (Nat.add_pos_left context.pos _)
    · simpa only [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
        nested_ratio context.val (context.val + first.val) second.val
          (Nat.add_pos_left context.pos _)

/-- Proportional scheduling satisfies the swap and reassociation laws consumed
by PolyFun's scheduled sampler-factorization bridge. -/
theorem isCoherent : BinaryScheduler.IsCoherent outputRel binary :=
  isFlat.isCoherent

/-- The mass-aware open-process theory instantiated with proportional
`ProbComp` scheduling. -/
noncomputable abbrev theory (Party : Type u) : OpenTheory :=
  scheduledOpenTheory Party ProbComp binary

/-- Equal scheduler mass together with sampler equivalence at `outputRel`, as a
congruence on `theory Party`. -/
noncomputable abbrev samplerCongruence (Party : Type u) : (theory Party).Congruence :=
  scheduledOpenTheory.samplerCongruence Party ProbComp binary outputRel

/-- `theory Party` modulo `samplerCongruence Party`. -/
noncomputable abbrev quotientTheory (Party : Type u) : OpenTheory :=
  (theory Party).quotient (samplerCongruence Party)

/-- The proportional theory modulo output-probability sampler equivalence
satisfies plug factorization: coherence of `binary` supplies the scheduler
transport facts, and `outputRel_isBindCongr` makes the relation a congruence. -/
instance hasPlugFactorization_quotientTheory (Party : Type u) :
    OpenTheory.HasPlugFactorization (quotientTheory Party) :=
  scheduledOpenTheory.hasPlugFactorization_quotient_samplerCongruence
    Party ProbComp binary outputRel isCoherent

end ProportionalScheduler

end UC
end Interaction
