/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.NoticingTape
public import HashSig.SLHDSA.SHAKE128s.Proof.BlockViews
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsConcentrationSharper
import VCVio.OracleComp.EvalDist.Sum

/-!
# Coverage when a served target may also disclose

The game's coverage event is wider than a target digest covered by the **disclosing block**
alone: a digest the adversary queried *before* the signer asked for it is filed as a target, and
if a later signature serves it, it discloses too. Ruling that out would cost one unit of
`2 ^ -128` per message-class query, and the ledger has no unit to spare for it, because the same
query is already a coverage target and a guess at `SK.prf`.

This file charges the wider event. A target cell `t` is covered by the disclosing block
together with the target cells that **fired**: cells whose input a later signature served. The
charge is

    Pr[¬ good block] + E[length] · 2 ^ -129 + E[length] · rightLength · 2 ^ -303,
so at any `rightLength ≤ 2 ^ 128` the fired cells cost a sliver of the half unit the sharper
load cap (`2 ^ 102`) leaves free.

**Why the fired cells are cheap.** The covering witnesses for `t` that are themselves target cells
all sit at `t`'s own FORS instance. If there are none, `t` is covered by the block — the first-order
term. If there is exactly one, `j`, then `t` is covered by the block together with `j`'s view
(`HelpedBy`), and two facts multiply: `j` fired, which a fresh `PRF_msg` draw decides at
`2 ^ -128` (`hthin1`), and two independent uniform views at one instance cover each other's leaves
with probability at most `2 ^ -177` (`prob_helpedBy_le`). If there are two, two fired cells share an
@[expose] instance: `2 ^ -256` for the two draws (`hthin2`) and `2 ^ -63` for the instance.

**What the run has to supply** is the two thinning bounds and one causality fact, all stated per
pair of blocks so they are facts about the run rather than about the blocks' law:

* `hcausal` — whether the run reaches target cell `index` does not depend on any cell at or after
  it. `NoticingTape.prob_selected_hit_le_of_causal` needs only `cell = index`; the pairs here also
  need later cells, because the helper may be read after the target was reached.
* `hthin1`, `hthin2` — reaching a cell and then seeing it fire costs `2 ^ -128` per cell.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.FiredCoverage

variable {α β : Type}

open DigestTape NoticingTape BlockViews ForsCoverage

/-! ## Two views at one instance -/

/-- **A target covered by the disclosures together with one helper view at its own instance.** -/
@[expose] def HelpedBy (revealed : Disclosures) (target helper : View) : Prop :=
  helper.1 = target.1 ∧
    ∀ tree, target.2 tree ∈ revealed target.1 tree ∨ helper.2 tree = target.2 tree

/-- Whether a helper view covers a target is decidable. -/
instance (revealed : Disclosures) (target helper : View) :
    Decidable (HelpedBy revealed target helper) := by
  unfold HelpedBy
  infer_instance

/-- The leaf pairs one tree contributes: the target's leaf disclosed, or the helper's equal. -/
@[expose] def LeafPairs (shown : Finset Leaf) : Type :=
  {pair : Leaf × Leaf // pair.1 ∈ shown ∨ pair.2 = pair.1}

/-- The leaf pairs of one tree form a finite type. -/
instance (shown : Finset Leaf) : Fintype (LeafPairs shown) := by
  unfold LeafPairs
  infer_instance

/-- The helped pairs, as a dependent choice of instance and per-tree leaf pairs. -/
@[expose] def helpedEquiv (revealed : Disclosures) :
    (Σ index : Instance, (tree : Tree) → LeafPairs (revealed index tree)) ≃
      {pair : View × View // HelpedBy revealed pair.1 pair.2} where
  toFun choice := ⟨((choice.1, fun tree => (choice.2 tree).val.1),
      (choice.1, fun tree => (choice.2 tree).val.2)),
    rfl, fun tree => (choice.2 tree).property⟩
  invFun pair := ⟨pair.val.1.1, fun tree =>
    ⟨(pair.val.1.2 tree, pair.val.2.2 tree), by
      rcases pair.property.2 tree with hshown | hsame
      · exact Or.inl hshown
      · exact Or.inr hsame⟩⟩
  left_inv := by rintro ⟨index, leaves⟩; rfl
  right_inv := by
    rintro ⟨⟨⟨index, targetLeaves⟩, ⟨helperIndex, helperLeaves⟩⟩, hindex, htrees⟩
    simp only at hindex
    subst hindex
    rfl

/-- Pairs at one tree: every leaf of the shown set with any helper leaf, and every other leaf with
an equal helper leaf. -/
theorem card_leafPairs_le (shown : Finset Leaf) :
    Fintype.card (LeafPairs shown) ≤ 2 ^ 12 * (shown.card + 1) := by
  classical
  let cover : Finset (Leaf × Leaf) :=
    (shown ×ˢ (Finset.univ : Finset Leaf)) ∪ (Finset.univ.image fun leaf : Leaf => (leaf, leaf))
  have hmem : ∀ pair : LeafPairs shown, pair.val ∈ cover := by
    rintro ⟨pair, hpair⟩
    rcases hpair with hshown | hsame
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hshown, Finset.mem_univ _⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨pair.1, Finset.mem_univ _, ?_⟩)
      exact Prod.ext rfl hsame.symm
  have hinj : Fintype.card (LeafPairs shown) ≤ Fintype.card cover :=
    Fintype.card_le_of_injective (fun pair => ⟨pair.val, hmem pair⟩)
      (fun left right h => Subtype.ext (congrArg Subtype.val h :))
  rw [Fintype.card_coe] at hinj
  refine le_trans hinj (le_trans (Finset.card_union_le _ _) ?_)
  rw [Finset.card_product, Finset.card_univ]
  refine le_trans (Nat.add_le_add_left Finset.card_image_le _) ?_
  have hleaf : Fintype.card Leaf = 2 ^ 12 := by
    unfold ForsCoverage.Leaf MessageDigest.ForsLeaf forsHeight; exact Fintype.card_fin _
  rw [Finset.card_univ, hleaf, mul_add, mul_one, mul_comm]

/-- **The count of helped pairs.** -/
theorem card_helped_le (revealed : Disclosures) (loads : Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index) :
    (Finset.univ.filter fun pair : View × View => HelpedBy revealed pair.1 pair.2).card ≤
      ∑ index : Instance, (2 ^ 12) ^ 14 * (loads index + 1) ^ 14 := by
  classical
  rw [← Fintype.card_subtype, ← Fintype.card_congr (helpedEquiv revealed), Fintype.card_sigma]
  refine Finset.sum_le_sum fun index _ => ?_
  rw [Fintype.card_pi]
  calc ∏ tree : Tree, Fintype.card (LeafPairs (revealed index tree))
      ≤ ∏ _tree : Tree, 2 ^ 12 * (loads index + 1) :=
        Finset.prod_le_prod fun tree _ =>
          le_trans (card_leafPairs_le _)
            (Nat.mul_le_mul_left _ (Nat.succ_le_succ (hload index tree)))
    _ = (2 ^ 12) ^ 14 * (loads index + 1) ^ 14 := by
        have htree : Fintype.card ForsCoverage.Tree = 14 := by
          unfold ForsCoverage.Tree MessageDigest.ForsTree forsTrees; exact Fintype.card_fin _
        rw [Finset.prod_const, Finset.card_univ, htree, mul_pow]

/-- A load raised by one is at most twice the larger of one and itself. -/
theorem succ_pow_le (load : Nat) : (load + 1) ^ 14 ≤ 2 ^ 14 * (1 + load ^ 14) := by
  rcases Nat.eq_zero_or_pos load with rfl | hpos
  · norm_num
  · calc (load + 1) ^ 14 ≤ (2 * load) ^ 14 := Nat.pow_le_pow_left (by omega) 14
      _ = 2 ^ 14 * load ^ 14 := by rw [mul_pow]
      _ ≤ 2 ^ 14 * (1 + load ^ 14) := Nat.mul_le_mul_left _ (by omega)

set_option exponentiation.threshold 1024 in
/-- **Two uniform views at one instance cover each other rarely.** With the loads' fourteenth
moment at most `2 ^ 102`, a uniform target is covered by the disclosures together with an
independent uniform helper at its own instance with probability at most `2 ^ -177`. -/
theorem prob_helpedBy_le (revealed : Disclosures) (loads : Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102) :
    Pr{let pair ← ($ᵗ (View × View) : ProbComp (View × View))}[HelpedBy revealed pair.1 pair.2] ≤
      1 / ((2 ^ 177 : Nat) : ℝ≥0∞) := by
  classical
  have hsum : ∑ index : Instance, (2 ^ 12) ^ 14 * (loads index + 1) ^ 14 ≤ 2 ^ 285 := by
    have hone : ∑ index : Instance, (2 ^ 12) ^ 14 * (loads index + 1) ^ 14 ≤
        ∑ index : Instance, (2 ^ 12) ^ 14 * (2 ^ 14 * (1 + loads index ^ 14)) :=
      Finset.sum_le_sum fun index _ => Nat.mul_le_mul_left _ (succ_pow_le _)
    refine le_trans hone ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ]
    have hcard : Fintype.card Instance = 2 ^ 63 := by
      unfold ForsCoverage.Instance MessageDigest.Instance totalHeight
      exact Fintype.card_fin _
    rw [hcard, smul_eq_mul, mul_one]
    calc (2 ^ 12) ^ 14 * (2 ^ 14 * (2 ^ 63 + ∑ index : Instance, loads index ^ 14))
        ≤ (2 ^ 12) ^ 14 * (2 ^ 14 * (2 ^ 63 + 2 ^ 102)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left hmoment _))
      _ ≤ 2 ^ 285 := by norm_num
  rw [SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card (View × View) = 2 ^ 462 := by
    norm_num [View, Instance, ForsCoverage.Tree, Leaf, MessageDigest.View, MessageDigest.Instance,
      MessageDigest.ForsTree, MessageDigest.ForsLeaf, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, totalHeight, forsHeight, forsTrees]
  rw [hcard]
  calc ((Finset.univ.filter fun pair : View × View => HelpedBy revealed pair.1 pair.2).card :
        ℝ≥0∞) / ((2 ^ 462 : Nat) : ℝ≥0∞)
      ≤ ((2 ^ 285 : Nat) : ℝ≥0∞) / ((2 ^ 462 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div_right
          (Nat.cast_le.mpr ((card_helped_le revealed loads hload).trans hsum)) _
    _ = 1 / ((2 ^ 177 : Nat) : ℝ≥0∞) := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num

set_option exponentiation.threshold 1024 in
/-- **A uniform view lands on a given instance with probability `2 ^ -63`.** -/
theorem prob_instance_eq (index : Instance) :
    Pr{let view ← ($ᵗ View : ProbComp View)}[view.1 = index] ≤
      1 / ((2 ^ 63 : Nat) : ℝ≥0∞) := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hcount : (Finset.univ.filter fun view : View => view.1 = index).card = 2 ^ 168 := by
    have hset : (Finset.univ.filter fun view : View => view.1 = index) =
        Finset.univ.image fun leaves : ForsCoverage.Tree → Leaf => (index, leaves) := by
      ext view
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hview
        exact ⟨view.2, Prod.ext hview.symm rfl⟩
      · rintro ⟨leaves, rfl⟩
        rfl
    rw [hset, Finset.card_image_of_injective _ (fun left right h => (Prod.mk.inj h).2),
      Finset.card_univ]
    norm_num [ForsCoverage.Tree, Leaf, MessageDigest.ForsTree, MessageDigest.ForsLeaf,
      Fintype.card_fun, Fintype.card_fin, forsHeight, forsTrees]
  have hcard : Fintype.card View = 2 ^ 231 := by
    norm_num [View, Instance, ForsCoverage.Tree, Leaf, MessageDigest.View, MessageDigest.Instance,
      MessageDigest.ForsTree, MessageDigest.ForsLeaf, Fintype.card_prod, Fintype.card_fun,
      Fintype.card_fin, totalHeight, forsHeight, forsTrees]
  rw [hcount, hcard]
  apply le_of_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

/-! ## Expectations against a padded block, with one cell redrawn -/

/-- **An expectation against a bind is the outer expectation of the inner ones.** -/
theorem tsum_probOutput_bind {α β : Type} (outer : ProbComp α) (inner : α → ProbComp β)
    (f : β → ℝ≥0∞) :
    ∑' out, Pr{let x ← outer >>= inner}[x = out] * f out =
      ∑' value, Pr{let x ← outer}[x = value] *
        ∑' out, Pr{let x ← inner value}[x = out] * f out := by
  exact tsum_prEvent_bind_mul outer inner f

/-- **An expectation against a point mass is the value at the point.** -/
theorem tsum_probOutput_pure {β : Type} (point : β) (f : β → ℝ≥0∞) :
    ∑' out, Pr{let x ← (pure point : ProbComp β)}[x = out] * f out = f point := by
  exact tsum_prEvent_pure_mul point f

/-- **Redrawing one cell of a padded block keeps any expectation.** The expectation form of
`TapeFactor.evalDist_padding_set`. -/
theorem tsum_padding_set (length cell : Nat) (hcell : cell < length)
    (f : List HashOutput → ℝ≥0∞) :
    ∑' tape, Pr{let x ← padding length}[x = tape] * f tape =
      ∑' tape, Pr{let x ← padding length}[x = tape] *
        ∑' value, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = value] *
          f (tape.set cell value) := by
  classical
  have hlaw := TapeFactor.evalDist_padding_set length cell hcell
    (fun tape => (pure tape : ProbComp (List HashOutput)))
  simp only [bind_pure] at hlaw
  calc ∑' tape, Pr{let x ← padding length}[x = tape] * f tape
      = ∑' out, Pr{let x ← padding length >>= fun tape =>
          ($ᵗ HashOutput : ProbComp HashOutput) >>= fun value =>
            (pure (tape.set cell value) : ProbComp (List HashOutput))}[x = out] * f out :=
        tsum_congr fun out => by rw [hlaw.prEvent_eq (fun x => x = out)]
    _ = _ := by
        rw [tsum_prEvent_bind_mul]
        refine tsum_congr fun tape => congrArg _ ?_
        rw [tsum_prEvent_bind_mul]
        exact tsum_congr fun value => by rw [tsum_prEvent_pure_mul]

section Tape

variable {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ) (len : ρ → Nat)

/-- **The expected weight on the runs that reach target cell `index`**, with both blocks drawn
first. A weight that reads the blocks only is a fact about the blocks; this keeps it beside the
selection, which is what lets one cell be redrawn under it. -/
@[expose] noncomputable def reachMass (leftLength rightLength index : Nat)
    (weight : List HashOutput → List HashOutput → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' leftTape, Pr{let x ← padding leftLength}[x = leftTape] *
    ∑' rightTape, Pr{let x ← padding rightLength}[x = rightTape] *
      (weight leftTape rightTape * Pr{let z ← run leftTape rightTape}[index < len z])

open scoped Classical in
/-- **A block event beside the selection is a reach mass.** -/
theorem prEvent_reach_and_eq (leftLength rightLength index : Nat)
    (event : List HashOutput → List HashOutput → Prop) :
    Pr{let outcome ← blockRunOf run leftLength rightLength}[
        index < len outcome.2 ∧ event outcome.1.1 outcome.1.2] =
      reachMass run len leftLength rightLength index
        (fun leftTape rightTape => if event leftTape rightTape then 1 else 0) := by
  classical
  rw [blockRunOf, prEvent_bind_eq_tsum, reachMass]
  refine tsum_congr fun leftTape => congrArg _ ?_
  rw [prEvent_bind_eq_tsum]
  refine tsum_congr fun rightTape => congrArg _ ?_
  rw [prEvent_map]
  rw [prEvent_congr _ _ (fun z => event leftTape rightTape ∧ index < len z) fun z => and_comm,
    TapeFactor.prEvent_const_and]
  split <;> simp

/-- The selection alone is the reach mass of the unit weight. -/
theorem prEvent_reach_eq (leftLength rightLength index : Nat) :
    Pr{let outcome ← blockRunOf run leftLength rightLength}[index < len outcome.2] =
      reachMass run len leftLength rightLength index (fun _ _ => 1) := by
  classical
  have h := prEvent_reach_and_eq run len leftLength rightLength index (fun _ _ => True)
  simp only [and_true, ite_true] at h
  exact h

/-- **The blocked run's events, as a double expectation over the two blocks.** -/
theorem prEvent_blockRunOf_eq (leftLength rightLength : Nat)
    (event : (List HashOutput × List HashOutput) × ρ → Prop) :
    Pr{let x ← blockRunOf run leftLength rightLength}[event x] =
      ∑' leftTape, Pr{let x ← padding leftLength}[x = leftTape] *
        ∑' rightTape, Pr{let x ← padding rightLength}[x = rightTape] *
          Pr{let z ← run leftTape rightTape}[event ((leftTape, rightTape), z)] := by
  rw [blockRunOf, prEvent_bind_eq_tsum]
  refine tsum_congr fun leftTape => congrArg _ ?_
  rw [prEvent_bind_eq_tsum]
  refine tsum_congr fun rightTape => congrArg _ ?_
  rw [prEvent_map]

/-- **A constant comes out of a reach mass.** -/
theorem reachMass_const_mul (leftLength rightLength index : Nat) (constant : ℝ≥0∞)
    (weight : List HashOutput → List HashOutput → ℝ≥0∞) :
    reachMass run len leftLength rightLength index
        (fun leftTape rightTape => constant * weight leftTape rightTape) =
      constant * reachMass run len leftLength rightLength index weight := by
  simp only [reachMass, mul_assoc, mul_left_comm _ constant, ENNReal.tsum_mul_left]

/-- **Redrawing a cell the selection does not read keeps the reach mass**, with the weight
averaged over the redrawn cell. -/
theorem reachMass_resample (leftLength rightLength index cell : Nat) (hcell : cell < rightLength)
    (hcausal : ∀ (leftTape rightTape : List HashOutput) (value : HashOutput),
      Pr{let z ← run leftTape (rightTape.set cell value)}[index < len z] =
        Pr{let z ← run leftTape rightTape}[index < len z])
    (weight : List HashOutput → List HashOutput → ℝ≥0∞) :
    reachMass run len leftLength rightLength index weight =
      reachMass run len leftLength rightLength index (fun leftTape rightTape =>
        ∑' value, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = value] *
          weight leftTape (rightTape.set cell value)) := by
  rw [reachMass, reachMass]
  refine tsum_congr fun leftTape => congrArg _ ?_
  rw [tsum_padding_set rightLength cell hcell]
  refine tsum_congr fun rightTape => congrArg _ ?_
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun value => ?_
  rw [hcausal leftTape rightTape value, mul_assoc]

/-- **A later cell is reached only on runs that reach an earlier one.** -/
theorem reachMass_mono_index (leftLength rightLength : Nat) {early late : Nat}
    (horder : early ≤ late) (weight : List HashOutput → List HashOutput → ℝ≥0∞) :
    reachMass run len leftLength rightLength late weight ≤
      reachMass run len leftLength rightLength early weight := by
  refine ENNReal.tsum_le_tsum fun leftTape => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun rightTape => mul_le_mul' le_rfl ?_
  exact mul_le_mul' le_rfl (prEvent_mono _ _ _ fun z hlate => lt_of_le_of_lt horder hlate)

/-- **A thinning, integrated over the blocks.** An event of the run whose probability, for every
pair of blocks, is at most `rate` times that of reaching cell `index` costs `rate` times the reach
mass of any block event beside it. -/
theorem prob_thin_le (leftLength rightLength index : Nat) (thinned : ρ → Prop)
    (rate : ℝ≥0∞)
    (hthin : ∀ leftTape rightTape, Pr{let x ← run leftTape rightTape}[thinned x] ≤
      rate * Pr{let z ← run leftTape rightTape}[index < len z])
    (event : List HashOutput → List HashOutput → Prop)
    [∀ leftTape rightTape, Decidable (event leftTape rightTape)] :
    Pr{let outcome ← blockRunOf run leftLength rightLength}[
        thinned outcome.2 ∧ event outcome.1.1 outcome.1.2] ≤
      rate * reachMass run len leftLength rightLength index
        (fun leftTape rightTape => if event leftTape rightTape then 1 else 0) := by
  classical
  rw [← reachMass_const_mul, prEvent_blockRunOf_eq, reachMass]
  refine ENNReal.tsum_le_tsum fun leftTape => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun rightTape => mul_le_mul' le_rfl ?_
  by_cases hevent : event leftTape rightTape
  · rw [ite_eq_left hevent, mul_one]
    refine le_trans (le_of_eq (prEvent_congr _ _ _ fun z => ?_)) (hthin leftTape rightTape)
    simp [hevent]
  · rw [ite_eq_right hevent, mul_zero, zero_mul]
    exact le_of_eq (prEvent_eq_zero_of_forall_not _ _ fun z hz => hevent hz.2)

/-- **A weight bounded on the padded blocks costs its bound times the reach probability.** The
padded blocks have their lengths, so a bound need only hold there. -/
theorem reachMass_le_const_of_length (leftLength rightLength index : Nat)
    (weight : List HashOutput → List HashOutput → ℝ≥0∞) (bound : ℝ≥0∞)
    (hbound : ∀ leftTape rightTape, rightTape.length = rightLength →
      weight leftTape rightTape ≤ bound) :
    reachMass run len leftLength rightLength index weight ≤
      bound * Pr{let outcome ← blockRunOf run leftLength rightLength}[index < len outcome.2] := by
  classical
  rw [prEvent_reach_eq run len leftLength rightLength index,
    ← reachMass_const_mul run len leftLength rightLength index bound]
  refine ENNReal.tsum_le_tsum fun leftTape => mul_le_mul' le_rfl ?_
  refine ENNReal.tsum_le_tsum fun rightTape => ?_
  by_cases hmem : rightTape ∈ support (padding rightLength)
  · refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
    rw [mul_one]
    exact hbound leftTape rightTape (padding_length rightLength rightTape hmem)
  · rw [(prEvent_eq_zero_of_not_mem_support _) hmem, zero_mul, zero_mul]

end Tape

/-! ## The wide event, and how it falls into four -/

/-- The parsed view at one cell of a block. -/
@[expose] def cellView (tape : List HashOutput) (index : Nat) : View :=
  MessageDigest.parse (tape.getD index default)

/-- A witness view supplies the target's leaf at one tree, at the target's own instance. -/
@[expose] def Supplies (witness target : View) (tree : Tree) : Prop :=
  witness.1 = target.1 ∧ witness.2 tree = target.2 tree

/-- The disclosing block's loads are below the sharper cap. -/
@[expose] def GoodLeft (leftLength : Nat) (leftTape : List HashOutput) : Prop :=
  ∑ part, ForsDisclosureTape.loads (blockTape leftLength leftTape) part ^ 14 ≤ 2 ^ 102

/-- The disclosures of the whole disclosing block. -/
@[expose] def leftDisclosures (leftLength : Nat) (leftTape : List HashOutput) : Disclosures :=
  ForsDisclosureTape.disclosures (blockTape leftLength leftTape)

/-- **The wide coverage event, in the blocks' coordinates.** Some reached target cell has each of
its fourteen leaves supplied, at its own instance, by a cell of the disclosing block or by
another reached target cell that fired. -/
@[expose] def FiredCovered {ρ : Type} (len : ρ → Nat) (fired : ρ → Nat → Prop)
    (leftLength rightLength : Nat) (outcome : (List HashOutput × List HashOutput) × ρ) : Prop :=
  ∃ target < rightLength, target < len outcome.2 ∧ ∀ tree,
    (∃ cell < leftLength,
      Supplies (cellView outcome.1.1 cell) (cellView outcome.1.2 target) tree) ∨
    (∃ helper < rightLength, helper < len outcome.2 ∧ helper ≠ target ∧
      fired outcome.2 helper ∧
      Supplies (cellView outcome.1.2 helper) (cellView outcome.1.2 target) tree)

/-- A leaf supplied by a block cell is a disclosed leaf of the block. -/
theorem mem_leftDisclosures {leftLength : Nat} {leftTape : List HashOutput} {view : View}
    {tree : Tree}
    (hcell : ∃ cell < leftLength, Supplies (cellView leftTape cell) view tree) :
    view.2 tree ∈ leftDisclosures leftLength leftTape view.1 tree := by
  obtain ⟨cell, hlt, hinstance, hleaf⟩ := hcell
  refine Finset.mem_image.mpr ⟨⟨cell, hlt⟩, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hinstance
  · exact hleaf

open scoped Classical in
/-- **The wide event falls into four.** The block is bad; or the target is covered by the block
alone; or exactly one fired cell at its instance helps; or two fired cells share an instance. -/
theorem firedCovered_cases {ρ : Type} (len : ρ → Nat) (fired : ρ → Nat → Prop)
    (leftLength rightLength : Nat) (leftTape rightTape : List HashOutput) (z : ρ)
    (hcovered : FiredCovered len fired leftLength rightLength ((leftTape, rightTape), z)) :
    ¬ GoodLeft leftLength leftTape ∨
      (∃ target < rightLength, target < len z ∧ GoodLeft leftLength leftTape ∧
        Covered (leftDisclosures leftLength leftTape) (cellView rightTape target)) ∨
      (∃ target < rightLength, ∃ helper < rightLength, target ≠ helper ∧
        (helper < len z ∧ fired z helper) ∧
        (GoodLeft leftLength leftTape ∧ HelpedBy (leftDisclosures leftLength leftTape)
          (cellView rightTape target) (cellView rightTape helper))) ∨
      (∃ first < rightLength, ∃ second < rightLength, first < second ∧
        (second < len z ∧ fired z first ∧ fired z second) ∧
        (cellView rightTape first).1 = (cellView rightTape second).1) := by
  classical
  obtain ⟨target, htarget, hreached, htrees⟩ := hcovered
  by_cases hgood : GoodLeft leftLength leftTape
  swap
  · exact Or.inl hgood
  refine Or.inr ?_
  -- Two distinct fired cells at the target's instance.
  by_cases htwo : ∃ first < rightLength, ∃ second < rightLength, first ≠ second ∧
      first < len z ∧ second < len z ∧ fired z first ∧ fired z second ∧
      (cellView rightTape first).1 = (cellView rightTape target).1 ∧
      (cellView rightTape second).1 = (cellView rightTape target).1
  · obtain ⟨first, hfirst, second, hsecond, hne, hfirstLen, hsecondLen, hfirstFired,
      hsecondFired, hfirstInst, hsecondInst⟩ := htwo
    refine Or.inr (Or.inr ?_)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨first, hfirst, second, hsecond, hlt, ⟨hsecondLen, hfirstFired, hsecondFired⟩,
        hfirstInst.trans hsecondInst.symm⟩
    · exact ⟨second, hsecond, first, hfirst, hgt, ⟨hfirstLen, hsecondFired, hfirstFired⟩,
        hsecondInst.trans hfirstInst.symm⟩
  -- At most one; if there is one, it helps.
  by_cases hone : ∃ helper < rightLength, helper < len z ∧ helper ≠ target ∧ fired z helper ∧
      (cellView rightTape helper).1 = (cellView rightTape target).1
  · obtain ⟨helper, hhelper, hhelperLen, hne, hfired, hinstance⟩ := hone
    refine Or.inr (Or.inl ⟨target, htarget, helper, hhelper, hne.symm, ⟨hhelperLen, hfired⟩,
      hgood, hinstance, fun tree => ?_⟩)
    rcases htrees tree with hblock | ⟨other, hother, hotherLen, hotherNe, hotherFired,
      hotherInstance, hotherLeaf⟩
    · exact Or.inl (mem_leftDisclosures hblock)
    · by_cases hsame : other = helper
      · subst hsame
        exact Or.inr hotherLeaf
      · exact absurd ⟨other, hother, helper, hhelper, hsame, hotherLen, hhelperLen,
          hotherFired, hfired, hotherInstance, hinstance⟩ htwo
  · refine Or.inl ⟨target, htarget, hreached, hgood, fun tree => ?_⟩
    rcases htrees tree with hblock | ⟨other, hother, hotherLen, hotherNe, hotherFired,
      hotherInstance, -⟩
    · exact mem_leftDisclosures hblock
    · exact absurd ⟨other, hother, hotherLen, hotherNe, hotherFired, hotherInstance⟩ hone

/-! ## The two rates, at fresh answers -/

/-- An indicator's expectation is its event's probability. -/
theorem tsum_ite_eq_probEvent {α : Type} (computation : ProbComp α) (event : α → Prop)
    [DecidablePred event] :
    ∑' value, Pr{let x ← computation}[x = value] * (if event value then 1 else 0) =
      Pr{let x ← computation}[event x] := by
  rw [prEvent_eq_tsum_ite]
  refine tsum_congr fun value => ?_
  split <;> simp

/-- **Two fresh answers parse to two independent uniform views.** -/
theorem evalDist_parse_pair :
    ((fun pair : HashOutput × HashOutput =>
        (MessageDigest.parse pair.1, MessageDigest.parse pair.2)) <$>
      ($ᵗ (HashOutput × HashOutput) : ProbComp (HashOutput × HashOutput))) =ᵈ
      ($ᵗ (View × View) : ProbComp (View × View)) := by
  rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind]
  have hshape : ((fun pair : HashOutput × HashOutput =>
        (MessageDigest.parse pair.1, MessageDigest.parse pair.2)) <$>
      (do let left ← ($ᵗ HashOutput : ProbComp HashOutput)
          let right ← ($ᵗ HashOutput : ProbComp HashOutput)
          pure (left, right))) =
      (do let left ← MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)
          let right ← MessageDigest.parse <$> ($ᵗ HashOutput : ProbComp HashOutput)
          pure (left, right)) := by
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  rw [hshape]
  exact evalDist_parse_uniform.bind fun _ => evalDist_parse_uniform.bind fun _ => .rfl

open scoped Classical in
/-- **The pair rate at fresh answers**: two fresh answers parse to a helped pair with probability
at most `2 ^ -177`, as a double expectation. -/
theorem tsum_pair_helpedBy_le (revealed : Disclosures) (loads : Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102) :
    ∑' first, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = first] *
      ∑' second, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = second] *
        (if HelpedBy revealed (MessageDigest.parse first) (MessageDigest.parse second)
          then 1 else 0) ≤ 1 / ((2 ^ 177 : Nat) : ℝ≥0∞) := by
  classical
  have hdouble : (∑' first, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = first] *
      ∑' second, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = second] *
        (if HelpedBy revealed (MessageDigest.parse first) (MessageDigest.parse second)
          then 1 else 0)) =
      Pr{let pair ← ($ᵗ (HashOutput × HashOutput) : ProbComp (HashOutput × HashOutput))}[
        HelpedBy revealed (MessageDigest.parse pair.1) (MessageDigest.parse pair.2)] := by
    rw [SampleableType.uniformSample_prod_eq_bind, prEvent_bind_eq_tsum]
    refine tsum_congr fun first => congrArg _ ?_
    rw [prEvent_bind_eq_tsum]
    refine tsum_congr fun second => congrArg _ ?_
    rw [prEvent_pure]
  rw [hdouble]
  have hmap : Pr{let pair ← ($ᵗ (HashOutput × HashOutput) : ProbComp (HashOutput × HashOutput))}[
        HelpedBy revealed (MessageDigest.parse pair.1) (MessageDigest.parse pair.2)] =
      Pr{let pair ← ($ᵗ (View × View) : ProbComp (View × View))}[
        HelpedBy revealed pair.1 pair.2] :=
    (prEvent_map _ _ (fun pair : View × View => HelpedBy revealed pair.1 pair.2)).symm.trans
      (evalDist_parse_pair.prEvent_eq _)
  rw [hmap]
  exact prob_helpedBy_le revealed loads hload hmoment

open scoped Classical in
/-- **The instance rate at a fresh answer**, as an expectation. -/
theorem tsum_instance_eq_le (index : Instance) :
    ∑' value, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = value] *
      (if (MessageDigest.parse value).1 = index then 1 else 0) ≤
      1 / ((2 ^ 63 : Nat) : ℝ≥0∞) := by
  classical
  rw [tsum_ite_eq_probEvent]
  have hmap : Pr{let value ← ($ᵗ HashOutput : ProbComp HashOutput)}[
        (MessageDigest.parse value).1 = index] =
      Pr{let view ← ($ᵗ View : ProbComp View)}[view.1 = index] :=
    (prEvent_map _ _ (fun view : View => view.1 = index)).symm.trans
      (evalDist_parse_uniform.prEvent_eq _)
  rw [hmap]
  exact prob_instance_eq index

/-- Reading back the cell just overwritten. -/
theorem cellView_set_self {tape : List HashOutput} {index : Nat} (hindex : index < tape.length)
    (value : HashOutput) : cellView (tape.set index value) index = MessageDigest.parse value := by
  simp [cellView, List.getD_eq_getElem?_getD, hindex]

/-- Reading a cell other than the one overwritten. -/
theorem cellView_set_ne {tape : List HashOutput} {index other : Nat} (hne : index ≠ other)
    (value : HashOutput) : cellView (tape.set index value) other = cellView tape other := by
  simp [cellView, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

/-! ## The charges, cell by cell -/

/-- Two expectations commute. -/
theorem tsum_tsum_swap (f : HashOutput → HashOutput → ℝ≥0∞) :
    ∑' first, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = first] *
      ∑' second, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = second] * f first second =
    ∑' second, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = second] *
      ∑' first, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = first] * f first second := by
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun second => tsum_congr fun first => by ring

section Charges

variable {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ) (len : ρ → Nat)

open scoped Classical in
/-- **One fired helper, at the reach mass of the helper's cell.** Redraw the later of the two
cells and then the earlier: what is left is the pair rate, paid once per reached cell. -/
theorem reachMass_helped_le (leftLength rightLength target helper : Nat)
    (htarget : target < rightLength) (hhelper : helper < rightLength) (hne : target ≠ helper)
    (hcausal : ∀ (index cell : Nat) (leftTape rightTape : List HashOutput) (value : HashOutput),
      index ≤ cell →
        Pr{let z ← run leftTape (rightTape.set cell value)}[index < len z] =
          Pr{let z ← run leftTape rightTape}[index < len z]) :
    reachMass run len leftLength rightLength helper (fun leftTape rightTape =>
        if GoodLeft leftLength leftTape ∧ HelpedBy (leftDisclosures leftLength leftTape)
            (cellView rightTape target) (cellView rightTape helper) then 1 else 0) ≤
      1 / ((2 ^ 177 : Nat) : ℝ≥0∞) *
        (Pr{let outcome ← blockRunOf run leftLength rightLength}[target < len outcome.2] +
          Pr{let outcome ← blockRunOf run leftLength rightLength}[helper < len outcome.2]) := by
  classical
  -- The pair rate, once both cells are fresh.
  have hpair : ∀ leftTape : List HashOutput,
      ∑' w, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = w] *
        ∑' v, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = v] *
          (if GoodLeft leftLength leftTape ∧ HelpedBy (leftDisclosures leftLength leftTape)
            (MessageDigest.parse w) (MessageDigest.parse v) then 1 else 0) ≤
        1 / ((2 ^ 177 : Nat) : ℝ≥0∞) := by
    intro leftTape
    by_cases hgood : GoodLeft leftLength leftTape
    · simp only [hgood, true_and]
      exact tsum_pair_helpedBy_le (leftDisclosures leftLength leftTape)
        (ForsDisclosureTape.loads (blockTape leftLength leftTape))
        (fun part tree => ForsDisclosureTape.disclosures_card_le_loads _ part tree) hgood
    · simp only [hgood, false_and, ↓reduceIte, mul_zero, tsum_zero]
      exact zero_le
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- the target is the earlier cell
    rw [reachMass_resample run len leftLength rightLength helper helper hhelper
      (fun leftTape rightTape value => hcausal helper helper leftTape rightTape value le_rfl)]
    refine le_trans (reachMass_mono_index run len leftLength rightLength (le_of_lt hlt) _) ?_
    rw [reachMass_resample run len leftLength rightLength target target htarget
      (fun leftTape rightTape value => hcausal target target leftTape rightTape value le_rfl)]
    refine le_trans (reachMass_le_const_of_length run len leftLength rightLength target _ _
      fun leftTape rightTape hlength => ?_) (mul_le_mul' le_rfl le_self_add)
    refine le_of_eq_of_le (tsum_congr fun w => congrArg _ (tsum_congr fun v => ?_))
      (hpair leftTape)
    rw [cellView_set_ne (Ne.symm hne), cellView_set_self (by rw [hlength]; exact htarget),
      cellView_set_self (by rw [List.length_set, hlength]; exact hhelper)]
  · -- the helper is the earlier cell
    rw [reachMass_resample run len leftLength rightLength helper target htarget
      (fun leftTape rightTape value => hcausal helper target leftTape rightTape value
        (le_of_lt hgt))]
    rw [reachMass_resample run len leftLength rightLength helper helper hhelper
      (fun leftTape rightTape value => hcausal helper helper leftTape rightTape value le_rfl)]
    refine le_trans (reachMass_le_const_of_length run len leftLength rightLength helper _ _
      fun leftTape rightTape hlength => ?_) (mul_le_mul' le_rfl le_add_self)
    refine le_of_eq_of_le ?_ (hpair leftTape)
    rw [tsum_tsum_swap]
    refine tsum_congr fun w => congrArg _ (tsum_congr fun v => ?_)
    rw [cellView_set_self (by rw [List.length_set, hlength]; exact htarget),
      cellView_set_ne hne, cellView_set_self (by rw [hlength]; exact hhelper)]

open scoped Classical in
/-- **Two cells at one instance, at the reach mass of the earlier one.** Redraw the later. -/
theorem reachMass_sameInstance_le (leftLength rightLength first second : Nat)
    (hsecond : second < rightLength) (horder : first < second)
    (hcausal : ∀ (index cell : Nat) (leftTape rightTape : List HashOutput) (value : HashOutput),
      index ≤ cell →
        Pr{let z ← run leftTape (rightTape.set cell value)}[index < len z] =
          Pr{let z ← run leftTape rightTape}[index < len z]) :
    reachMass run len leftLength rightLength first (fun _ rightTape =>
        if (cellView rightTape first).1 = (cellView rightTape second).1 then 1 else 0) ≤
      1 / ((2 ^ 63 : Nat) : ℝ≥0∞) *
        Pr{let outcome ← blockRunOf run leftLength rightLength}[first < len outcome.2] := by
  classical
  rw [reachMass_resample run len leftLength rightLength first second hsecond
    (fun leftTape rightTape value => hcausal first second leftTape rightTape value
      (le_of_lt horder))]
  refine reachMass_le_const_of_length run len leftLength rightLength first _ _
    fun leftTape rightTape hlength => ?_
  refine le_of_eq_of_le (tsum_congr fun v => congrArg _ ?_)
    (tsum_instance_eq_le (cellView rightTape first).1)
  rw [cellView_set_ne (Nat.ne_of_gt horder), cellView_set_self (by rw [hlength]; exact hsecond)]
  exact if_congr eq_comm rfl rfl

end Charges

/-! ## The whole charge -/

/-- A blocked outcome carries two padded blocks. -/
theorem mem_support_blockRunOf {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (leftLength rightLength : Nat) {outcome : (List HashOutput × List HashOutput) × ρ}
    (hmem : outcome ∈ support (blockRunOf run leftLength rightLength)) :
    outcome.1.1 ∈ support (padding leftLength) ∧ outcome.1.2 ∈ support (padding rightLength) := by
  rw [blockRunOf, mem_support_bind_iff] at hmem
  obtain ⟨leftTape, hleft, hrest⟩ := hmem
  rw [mem_support_bind_iff] at hrest
  obtain ⟨rightTape, hright, hinner⟩ := hrest
  rw [support_map] at hinner
  obtain ⟨z, -, rfl⟩ := hinner
  exact ⟨hleft, hright⟩

open scoped Classical in
/-- **A bad disclosing block is a fact about the block alone**, at the sharper cap. -/
theorem prob_not_goodLeft_le {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62) :
    Pr{let outcome ← blockRunOf run leftLength rightLength}[¬ GoodLeft leftLength outcome.1.1] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 := by
  classical
  have hblock : Pr{let block ← padding leftLength}[¬ GoodLeft leftLength block] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 := by
    have hevent : Pr{let block ← padding leftLength}[¬ GoodLeft leftLength block] =
        Pr{let tape ← ($ᵗ (ForsDisclosureTape.Tape leftLength) :
            ProbComp (ForsDisclosureTape.Tape leftLength))}[
          2 ^ 102 < ∑ part, ForsDisclosureTape.loads tape part ^ 14] := by
      refine (prEvent_congr _ _
        (fun block => 2 ^ 102 < ∑ part,
          ForsDisclosureTape.loads (blockTape leftLength block) part ^ 14)
        fun block => by simp only [GoodLeft, not_le]).trans ?_
      exact (prEvent_map _ _ (fun tape : ForsDisclosureTape.Tape leftLength =>
        2 ^ 102 < ∑ part, ForsDisclosureTape.loads tape part ^ 14)).symm.trans
        ((evalDist_blockTape leftLength).prEvent_eq _)
    rw [hevent]
    exact ForsDisclosureTape.bad_load_probability_sharper leftLength hcap
  refine le_trans ?_ hblock
  rw [prEvent_blockRunOf_eq, ← tsum_ite_eq_probEvent]
  refine ENNReal.tsum_le_tsum fun leftTape => mul_le_mul' le_rfl ?_
  by_cases hgood : GoodLeft leftLength leftTape
  · simp [hgood]
  · rw [ite_eq_left hgood]
    exact le_trans (ENNReal.tsum_le_tsum fun _ => mul_le_of_le_one_right' (prEvent_le_one _))
      (tsum_prEvent_le_one _)

set_option exponentiation.threshold 1024 in
/-- The constants of the second-order terms fit under `2 ^ -303`. -/
theorem second_order_constants :
    2 * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞) * (1 / ((2 ^ 177 : Nat) : ℝ≥0∞))) +
        1 / ((2 ^ 256 : Nat) : ℝ≥0∞) * (1 / ((2 ^ 63 : Nat) : ℝ≥0∞)) ≤
      1 / ((2 ^ 303 : Nat) : ℝ≥0∞) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]
  norm_num

open scoped Classical in
/-- **The coverage charge with fired cells admitted as witnesses.**

The first-order term is the block's: `2 ^ -129` per expected target, at the sharper cap. The
fired cells cost `rightLength · 2 ^ -303` per expected target, which at any `rightLength ≤ 2 ^ 128`
is far inside the other half unit. -/
theorem prob_firedCovered_le {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (rightOfResult : ρ → Record) (fired : ρ → Nat → Prop)
    (leftLength rightLength : Nat) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hcausal : ∀ (index cell : Nat) (leftTape rightTape : List HashOutput) (value : HashOutput),
      index ≤ cell →
        Pr{let z ← run leftTape (rightTape.set cell value)}[index < (rightOfResult z).length] =
          Pr{let z ← run leftTape rightTape}[index < (rightOfResult z).length])
    (hthin1 : ∀ (index : Nat) (leftTape rightTape : List HashOutput),
      Pr{let z ← run leftTape rightTape}[index < (rightOfResult z).length ∧ fired z index] ≤
        1 / ((2 ^ 128 : Nat) : ℝ≥0∞) *
          Pr{let z ← run leftTape rightTape}[index < (rightOfResult z).length])
    (hthin2 : ∀ (first second : Nat) (leftTape rightTape : List HashOutput), first < second →
      Pr{let z ← run leftTape rightTape}[second < (rightOfResult z).length ∧ fired z first ∧
          fired z second] ≤
        1 / ((2 ^ 256 : Nat) : ℝ≥0∞) *
          Pr{let z ← run leftTape rightTape}[first < (rightOfResult z).length]) :
    Pr{let x ← blockRunOf run leftLength rightLength}[
        (FiredCovered (fun z => (rightOfResult z).length) fired leftLength rightLength) x] ≤
      (1 : ℝ≥0∞) / 2 ^ 126 +
        (∑' outcome, Pr{let x ← blockRunOf run leftLength rightLength}[x = outcome] *
            (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞)) *
          (1 / ((2 ^ 129 : Nat) : ℝ≥0∞)) +
        (rightLength : ℝ≥0∞) *
          (∑' outcome, Pr{let x ← blockRunOf run leftLength rightLength}[x = outcome] *
            (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞)) *
          (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by
  classical
  set len : ρ → Nat := fun z => (rightOfResult z).length with hlen
  set expectation := ∑' outcome, Pr{let x ← blockRunOf run leftLength rightLength}[x = outcome] *
    (((rightOfResult outcome.2).length : Nat) : ℝ≥0∞) with hexpectation
  set reach : Nat → ℝ≥0∞ := fun index =>
    Pr{let outcome ← blockRunOf run leftLength rightLength}[index < len outcome.2] with hreach
  have hsum : ∑ index : Fin rightLength, reach index.val ≤ expectation :=
    sum_prob_selected_le_expected_of run rightOfResult leftLength rightLength
  -- The four events.
  set eventA : (List HashOutput × List HashOutput) × ρ → Prop := fun outcome =>
    ∃ index : Fin rightLength, index.val < (rightOfResult outcome.2).length ∧
      GoodLeft leftLength outcome.1.1 ∧
        ∃ value, outcome.1.2[index.val]? = some value ∧ BlockHit leftLength outcome.1.1 value
    with heventA
  set eventB : (List HashOutput × List HashOutput) × ρ → Prop := fun outcome =>
    ∃ pair ∈ (Finset.univ : Finset (Fin rightLength × Fin rightLength)),
      pair.1.val ≠ pair.2.val ∧
        ((pair.2.val < len outcome.2 ∧ fired outcome.2 pair.2.val) ∧
          (GoodLeft leftLength outcome.1.1 ∧ HelpedBy (leftDisclosures leftLength outcome.1.1)
            (cellView outcome.1.2 pair.1.val) (cellView outcome.1.2 pair.2.val))) with heventB
  set eventC : (List HashOutput × List HashOutput) × ρ → Prop := fun outcome =>
    ∃ pair ∈ (Finset.univ : Finset (Fin rightLength × Fin rightLength)),
      pair.1.val < pair.2.val ∧
        ((pair.2.val < len outcome.2 ∧ fired outcome.2 pair.1.val ∧ fired outcome.2 pair.2.val) ∧
          (cellView outcome.1.2 pair.1.val).1 = (cellView outcome.1.2 pair.2.val).1)
    with heventC
  have hsplit : Pr{let x ← blockRunOf run leftLength rightLength}[
        FiredCovered len fired leftLength rightLength x] ≤
      Pr{let outcome ← blockRunOf run leftLength rightLength}[¬ GoodLeft leftLength outcome.1.1] +
        (Pr{let x ← blockRunOf run leftLength rightLength}[eventA x] +
          (Pr{let x ← blockRunOf run leftLength rightLength}[eventB x] +
            Pr{let x ← blockRunOf run leftLength rightLength}[eventC x])) := by
    refine le_trans (prEvent_mono_of_support _ _ (fun outcome =>
      ¬ GoodLeft leftLength outcome.1.1 ∨ (eventA outcome ∨ (eventB outcome ∨ eventC outcome)))
      fun outcome hmem hcovered => ?_) ?_
    · have hlength := padding_length rightLength outcome.1.2
        (mem_support_blockRunOf run leftLength rightLength hmem).2
      rcases firedCovered_cases len fired leftLength rightLength outcome.1.1 outcome.1.2
          outcome.2 hcovered with hbad | ⟨target, htarget, hreached, hgood, hcov⟩ |
          ⟨target, htarget, helper, hhelper, hne, hthin, hhelp⟩ |
          ⟨first, hfirst, second, hsecond, horder, hthin, hinstance⟩
      · exact Or.inl hbad
      · refine Or.inr (Or.inl ⟨⟨target, htarget⟩, hreached, hgood,
          outcome.1.2.getD target default, ?_, hcov⟩)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlength]; exact htarget)]
        rfl
      · exact Or.inr (Or.inr (Or.inl ⟨(⟨target, htarget⟩, ⟨helper, hhelper⟩),
          Finset.mem_univ _, hne, hthin, hhelp⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨(⟨first, hfirst⟩, ⟨second, hsecond⟩),
          Finset.mem_univ _, horder, hthin, hinstance⟩))
    · refine le_trans (prEvent_or_le _ _ _) (add_le_add le_rfl ?_)
      refine le_trans (prEvent_or_le _ _ _) (add_le_add le_rfl ?_)
      exact prEvent_or_le _ _ _
  -- The block alone.
  have hbad := prob_not_goodLeft_le run leftLength rightLength hcap
  -- The first-order term.
  have hfirstOrder : Pr{let x ← blockRunOf run leftLength rightLength}[eventA x] ≤
      expectation * (1 / ((2 ^ 129 : Nat) : ℝ≥0∞)) :=
    NoticingTape.prob_exists_hit_le_expected_of_causal run rightOfResult leftLength rightLength
      (GoodLeft leftLength) (BlockHit leftLength) (1 / ((2 ^ 129 : Nat) : ℝ≥0∞))
      (fun leftTape hgood => by
        refine le_trans (le_of_eq ?_) (ForsCoverage.fresh_coverage_le_sharper
          (ForsDisclosureTape.disclosures (blockTape leftLength leftTape))
          (ForsDisclosureTape.loads (blockTape leftLength leftTape))
          (fun part tree => ForsDisclosureTape.disclosures_card_le_loads _ part tree) hgood)
        exact (prEvent_map _ _ (fun view : View => Covered
          (ForsDisclosureTape.disclosures (blockTape leftLength leftTape)) view)).symm.trans
          (evalDist_parse_uniform.prEvent_eq _))
      (fun index leftTape rightTape value => hcausal index index leftTape rightTape value le_rfl)
  -- One fired helper.
  set pairRate : ℝ≥0∞ := 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) * (1 / ((2 ^ 177 : Nat) : ℝ≥0∞))
    with hpairRate
  have hhelped : Pr{let x ← blockRunOf run leftLength rightLength}[eventB x] ≤
      ∑ pair : Fin rightLength × Fin rightLength,
        pairRate * (reach pair.1.val + reach pair.2.val) := by
    refine le_trans (prEvent_exists_finset_le _ _ _) (Finset.sum_le_sum fun pair _ => ?_)
    by_cases hsame : pair.1.val = pair.2.val
    · rw [prEvent_eq_zero_of_forall_not _ _ fun outcome hevent => hevent.1 hsame]
      exact zero_le
    · rw [prEvent_congr _ _ (fun outcome : (List HashOutput × List HashOutput) × ρ =>
          (pair.2.val < len outcome.2 ∧ fired outcome.2 pair.2.val) ∧
            (GoodLeft leftLength outcome.1.1 ∧
              HelpedBy (leftDisclosures leftLength outcome.1.1)
                (cellView outcome.1.2 pair.1.val) (cellView outcome.1.2 pair.2.val)))
          (fun outcome => ⟨fun h => h.2, fun h => ⟨hsame, h⟩⟩)]
      refine le_trans (prob_thin_le run len leftLength rightLength pair.2.val
        (fun z => pair.2.val < len z ∧ fired z pair.2.val) _
        (fun leftTape rightTape => hthin1 pair.2.val leftTape rightTape)
        (fun leftTape rightTape => GoodLeft leftLength leftTape ∧
          HelpedBy (leftDisclosures leftLength leftTape)
            (cellView rightTape pair.1.val) (cellView rightTape pair.2.val))) ?_
      rw [hpairRate, mul_assoc]
      exact mul_le_mul' le_rfl (reachMass_helped_le run len leftLength rightLength
        pair.1.val pair.2.val pair.1.isLt pair.2.isLt hsame hcausal)
  -- Two fired cells at one instance.
  set twoRate : ℝ≥0∞ := 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) * (1 / ((2 ^ 63 : Nat) : ℝ≥0∞))
    with htwoRate
  have htwo : Pr{let x ← blockRunOf run leftLength rightLength}[eventC x] ≤
      ∑ pair : Fin rightLength × Fin rightLength, twoRate * reach pair.1.val := by
    refine le_trans (prEvent_exists_finset_le _ _ _) (Finset.sum_le_sum fun pair _ => ?_)
    by_cases horder : pair.1.val < pair.2.val
    · rw [prEvent_congr _ _ (fun outcome : (List HashOutput × List HashOutput) × ρ =>
          (pair.2.val < len outcome.2 ∧ fired outcome.2 pair.1.val ∧
              fired outcome.2 pair.2.val) ∧
            (cellView outcome.1.2 pair.1.val).1 = (cellView outcome.1.2 pair.2.val).1)
          (fun outcome => ⟨fun h => h.2, fun h => ⟨horder, h⟩⟩)]
      refine le_trans (prob_thin_le run len leftLength rightLength pair.1.val
        (fun z => pair.2.val < len z ∧ fired z pair.1.val ∧ fired z pair.2.val) _
        (fun leftTape rightTape => hthin2 pair.1.val pair.2.val leftTape rightTape horder)
        (fun _ rightTape =>
          (cellView rightTape pair.1.val).1 = (cellView rightTape pair.2.val).1)) ?_
      rw [htwoRate, mul_assoc]
      exact mul_le_mul' le_rfl (reachMass_sameInstance_le run len leftLength rightLength
        pair.1.val pair.2.val pair.2.isLt horder hcausal)
    · rw [prEvent_eq_zero_of_forall_not _ _ fun outcome hevent => horder hevent.1]
      exact zero_le
  -- Summing the pairs.
  have hpairs : ∑ pair : Fin rightLength × Fin rightLength,
        pairRate * (reach pair.1.val + reach pair.2.val) +
      ∑ pair : Fin rightLength × Fin rightLength, twoRate * reach pair.1.val ≤
      (rightLength : ℝ≥0∞) * expectation * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by
    have hfirst : ∑ pair : Fin rightLength × Fin rightLength, reach pair.1.val =
        (rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.mul_sum]
    have hsecond : ∑ pair : Fin rightLength × Fin rightLength, reach pair.2.val =
        (rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hfirst, hsecond]
    calc pairRate * ((rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val +
            (rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val) +
          twoRate * ((rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val)
        = (2 * pairRate + twoRate) *
            ((rightLength : ℝ≥0∞) * ∑ index : Fin rightLength, reach index.val) := by ring
      _ ≤ (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) * ((rightLength : ℝ≥0∞) * expectation) :=
          mul_le_mul' second_order_constants (mul_le_mul' le_rfl hsum)
      _ = (rightLength : ℝ≥0∞) * expectation * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by ring
  calc Pr{let x ← blockRunOf run leftLength rightLength}[
        FiredCovered len fired leftLength rightLength x]
      ≤ _ := hsplit
    _ ≤ (1 : ℝ≥0∞) / 2 ^ 126 + (expectation * (1 / ((2 ^ 129 : Nat) : ℝ≥0∞)) +
          ((rightLength : ℝ≥0∞) * expectation * (1 / ((2 ^ 303 : Nat) : ℝ≥0∞)))) :=
        add_le_add hbad (add_le_add hfirstOrder
          (le_trans (add_le_add hhelped htwo) hpairs))
    _ = _ := by ring

end SlhDsaSecurity.FiredCoverage
