/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FiredCoverage
import all HashSig.SLHDSA.SHAKE128s.Proof.FiredCoverage
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsLoadTail
import VCVio.OracleComp.EvalDist.Sum

/-!
# FORS load tails and coverage from consumed signer prefixes

Symmetric load tails factor against events determined before a second signer answer.
A left-dependent disclosure family bounds coverage from the consumed prefix
on the same full tape law.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.FiredCoverage

open DigestTape NoticingTape BlockViews ForsCoverage TapeFactor

private theorem list_eq_of_set_invariant {α β : Type}
    (xs ys : List α) (hlen : xs.length = ys.length)
    (f : List α → β) (hf : ∀ tape cell value, f (tape.set cell value) = f tape) :
    f xs = f ys := by
  induction xs generalizing ys f with
  | nil =>
      have hys : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      rfl
  | cons x xs ih =>
      cases ys with
      | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
      | cons y ys =>
          calc
            f (x :: xs) = f (y :: xs) := by simpa only [List.set_cons_zero] using
              (hf (x :: xs) 0 y).symm
            _ = f (y :: ys) := ih ys (Nat.succ.inj hlen) (fun tail => f (y :: tail))
              (fun tail cell value => by
                simpa only [List.set_cons_succ] using hf (y :: tail) (cell + 1) value)

private theorem head_event_eq_of_tail_causal {ρ : Type}
    (rest : List HashOutput → ProbComp ρ) (event : ρ → Prop)
    (hcausal : ∀ tape cell value, 1 ≤ cell →
      (Pr{let z ← rest (tape.set cell value)}[event z]) =
        Pr{let z ← rest tape}[event z])
    (head : HashOutput) (tail other : List HashOutput) (hlen : tail.length = other.length) :
    (Pr{let z ← rest (head :: tail)}[event z]) =
      Pr{let z ← rest (head :: other)}[event z] := by
  apply list_eq_of_set_invariant tail other hlen
    (fun tape => Pr{let z ← rest (head :: tape)}[event z])
  intro tape cell value
  simpa only [List.set_cons_succ] using hcausal (head :: tape) (cell + 1) value (by omega)

private theorem blockTape_cons (remaining : Nat) (head : HashOutput)
    (tail : List HashOutput) :
    blockTape (remaining + 1) (head :: tail) =
      Fin.cons (MessageDigest.parse head) (blockTape remaining tail) := by
  funext index
  refine Fin.cases ?_ (fun j => ?_) index
  · simp only [blockTape, Fin.cons_zero, Fin.val_zero, List.getD_cons_zero]
  · simp only [blockTape, Fin.cons_succ, Fin.val_succ, List.getD_cons_succ]

private theorem fixed_full_head_load_tail (remaining cutoff : Nat) (head : HashOutput) :
    Pr{let tail ← padding remaining}[
      cutoff < ∑ part, ForsDisclosureTape.loads
        (blockTape (remaining + 1) (head :: tail)) part ^ 14] =
    Pr{let tape ← padding (remaining + 1)}[
      cutoff < ∑ part, ForsDisclosureTape.loads
        (blockTape (remaining + 1) tape) part ^ 14] := by
  calc
    _ = Pr{let tail ← padding remaining}[
        cutoff < ∑ part, ForsDisclosureTape.loads
          (Fin.cons (MessageDigest.parse head) (blockTape remaining tail)) part ^ 14] :=
      prEvent_congr _ _ _ fun tail => by rw [blockTape_cons]
    _ = Pr{let tail ← ($ᵗ (ForsDisclosureTape.Tape remaining) : ProbComp _)}[
        cutoff < ∑ part, ForsDisclosureTape.loads
          (Fin.cons (MessageDigest.parse head) tail) part ^ 14] :=
      by
        simpa only [prEvent_map] using
          ((evalDist_blockTape remaining).prEvent_eq
            (fun tail : ForsDisclosureTape.Tape remaining => cutoff < ∑ part,
              ForsDisclosureTape.loads (Fin.cons (MessageDigest.parse head) tail) part ^ 14))
    _ = Pr{let tape ← ($ᵗ (ForsDisclosureTape.Tape (remaining + 1)) : ProbComp _)}[
        cutoff < ∑ part, ForsDisclosureTape.loads tape part ^ 14] :=
      ForsDisclosureTape.prEvent_uniform_tail_load_gt_eq_uniform_tape
        remaining cutoff (MessageDigest.parse head)
    _ = _ := by
      symm
      simpa only [prEvent_map] using
        ((evalDist_blockTape (remaining + 1)).prEvent_eq
          (fun tape : ForsDisclosureTape.Tape (remaining + 1) =>
            cutoff < ∑ part, ForsDisclosureTape.loads tape part ^ 14))

open scoped Classical in
private theorem prEvent_bind_eq_factor_of_support {α β : Type}
    (draw : ProbComp α) (rest : α → ProbComp β)
    (select : α → Prop) (event : β → Prop) (mass : ℝ≥0∞)
    (hmass : ∀ value ∈ support draw, (Pr{let z ← rest value}[event z]) = mass) :
    prEvent (draw >>= fun value => (fun z => select value ∧ event z) <$> rest value) =
      Pr{let value ← draw}[select value] * mass := by
  rw [prEvent_bind_eq_tsum_prEvent]
  calc
    _ = ∑' value, (if select value then Pr{let x ← draw}[x = value] else 0) * mass := by
      apply tsum_congr
      intro value
      change Pr{let x ← draw}[x = value] *
        Pr{let z ← rest value}[select value ∧ event z] = _
      rw [prEvent_const_and]
      by_cases hmem : value ∈ support draw
      · rw [hmass value hmem]
        by_cases hselect : select value <;> simp only [hselect, ↓reduceIte, mul_zero, zero_mul]
      · have hzero : Pr{let x ← draw}[x = value] = 0 :=
          prEvent_eq_zero_of_forall_mem_support draw _ fun x hx hxeq => hmem (hxeq ▸ hx)
        simp only [hzero, zero_mul, ite_self]
    _ = _ := by rw [ENNReal.tsum_mul_right, ← prEvent_eq_tsum_ite]

open scoped Classical in
/-- An event whose probability cannot see any left cell after the first factors
against a symmetric load-tail event on the full uniformly sampled left block. -/
theorem prEvent_bad_load_and_event_eq_mul
    {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (event : ρ → Prop) (remaining rightLength cutoff : Nat)
    (hcausal : ∀ (cell : Nat) (leftTape rightTape : List HashOutput)
        (value : HashOutput), 1 ≤ cell →
      (Pr{let z ← run (leftTape.set cell value) rightTape}[event z]) =
        Pr{let z ← run leftTape rightTape}[event z]) :
    Pr{let outcome ← blockRunOf run (remaining + 1) rightLength}[
      (cutoff < ∑ part,
        ForsDisclosureTape.loads (blockTape (remaining + 1) outcome.1.1) part ^ 14) ∧
          event outcome.2] =
      (Pr{let leftTape ← padding (remaining + 1)}[
        cutoff < ∑ part,
          ForsDisclosureTape.loads (blockTape (remaining + 1) leftTape) part ^ 14]) *
      Pr{let outcome ← blockRunOf run (remaining + 1) rightLength}[event outcome.2]
 := by
  classical
  let bad : List HashOutput → Prop := fun tape =>
    cutoff < ∑ part, ForsDisclosureTape.loads (blockTape (remaining + 1) tape) part ^ 14
  let rest : List HashOutput → ProbComp ρ := fun tape =>
    padding rightLength >>= fun rightTape => run tape rightTape
  let baseTail : List HashOutput := List.replicate remaining default
  let plain : HashOutput → ProbComp Prop := fun head =>
    padding remaining >>= fun tail => event <$> rest (head :: tail)
  let joint : HashOutput → ProbComp Prop := fun head =>
    padding remaining >>= fun tail => (fun z => bad (head :: tail) ∧ event z) <$>
      rest (head :: tail)
  let beta : ℝ≥0∞ := Pr{let tape ← padding (remaining + 1)}[bad tape]
  have hrest : ∀ tape cell value, 1 ≤ cell →
      (Pr{let z ← rest (tape.set cell value)}[event z]) =
        Pr{let z ← rest tape}[event z] := by
    intro tape cell value hcell
    simpa only [rest, map_bind] using prEvent_bind_congr_of_support (padding rightLength)
      (fun rightTape => event <$> run (tape.set cell value) rightTape)
      (fun rightTape => event <$> run tape rightTape)
      (fun rightTape _ => hcausal cell tape rightTape value hcell)
  have hinner (head : HashOutput) : prEvent (joint head) = beta * prEvent (plain head) := by
    let mass : ℝ≥0∞ := Pr{let z ← rest (head :: baseTail)}[event z]
    have hmass : ∀ tail ∈ support (padding remaining),
        (Pr{let z ← rest (head :: tail)}[event z]) = mass := by
      intro tail htail
      exact head_event_eq_of_tail_causal rest event hrest head tail baseTail
        ((padding_length remaining tail htail).trans
          (by simp only [baseTail, List.length_replicate]))
    have hplain : prEvent (plain head) = mass := by
      change prEvent (padding remaining >>= fun tail => event <$> rest (head :: tail)) = mass
      rw [prEvent_bind_eq_tsum_prEvent]
      exact tsum_prEvent_mul_of_const_on_support (padding remaining) hmass
    rw [hplain]
    exact (prEvent_bind_eq_factor_of_support (padding remaining)
      (fun tail => rest (head :: tail)) (fun tail => bad (head :: tail)) event mass hmass).trans
      (congrArg (fun probability => probability * mass)
        (fixed_full_head_load_tail remaining cutoff head))
  have hpadding : padding (remaining + 1) =
      (($ᵗ HashOutput : ProbComp HashOutput) >>= fun head =>
        padding remaining >>= fun tail => pure (head :: tail)) := rfl
  have hjoint :
      Pr{let outcome ← blockRunOf run (remaining + 1) rightLength}[
        (cutoff < ∑ part, ForsDisclosureTape.loads
          (blockTape (remaining + 1) outcome.1.1) part ^ 14) ∧ event outcome.2] =
      prEvent (($ᵗ HashOutput : ProbComp HashOutput) >>= joint) := by
    simp only [blockRunOf, hpadding, map_bind, Functor.map_map,
      bind_assoc, pure_bind, joint, rest, bad]
  have hplain :
      Pr{let outcome ← blockRunOf run (remaining + 1) rightLength}[event outcome.2] =
      prEvent (($ᵗ HashOutput : ProbComp HashOutput) >>= plain) := by
    simp only [blockRunOf, hpadding, map_bind, Functor.map_map,
      bind_assoc, pure_bind, plain, rest]
  rw [hjoint, hplain]
  change prEvent (($ᵗ HashOutput : ProbComp HashOutput) >>= joint) =
    beta * prEvent (($ᵗ HashOutput : ProbComp HashOutput) >>= plain)
  rw [prEvent_bind_eq_tsum_prEvent, prEvent_bind_eq_tsum_prEvent]
  calc
    _ = ∑' head, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = head] *
        (beta * prEvent (plain head)) := tsum_congr fun head => congrArg _ (hinner head)
    _ = _ := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro head
      ring

/-! ## A disclosure family chosen from the left block -/

private def loadMoment (length : Nat) (leftTape : List HashOutput) : Nat :=
  ∑ part, ForsDisclosureTape.loads (blockTape length leftTape) part ^ 14

private def disclosureCutoff (length : Nat) (leftTape : List HashOutput) : Nat :=
  if loadMoment length leftTape ≤ 9 * 2 ^ 99 then length else 1

private theorem loadMoment_one (leftTape : List HashOutput) : loadMoment 1 leftTape = 1 := by
  classical
  have hsingle : (Finset.univ : Finset (Fin 1)) = {0} := by ext j; simp [Fin.eq_zero j]
  have hload (part : Instance) :
      ForsDisclosureTape.loads (blockTape 1 leftTape) part =
        if part = (cellView leftTape 0).1 then 1 else 0 := by
    unfold ForsDisclosureTape.loads
    rw [hsingle]
    by_cases hpart : part = (cellView leftTape 0).1
    · subst part
      simp [blockTape, cellView]
    · have hne : (blockTape 1 leftTape (0 : Fin 1)).1 ≠ part := by
        simpa only [blockTape, cellView, Fin.val_zero] using Ne.symm hpart
      simp [hne, hpart]
  simp [loadMoment, hload]

private theorem cutoff_moment_le (length : Nat) (leftTape : List HashOutput) :
    loadMoment (disclosureCutoff length leftTape) leftTape ≤ 9 * 2 ^ 99 := by
  unfold disclosureCutoff
  split_ifs with hgood
  · exact hgood
  · rw [loadMoment_one]
    norm_num

private theorem blockHit_cutoff_rate (length : Nat) (leftTape : List HashOutput) :
    Pr{let value ← ($ᵗ HashOutput : ProbComp HashOutput)}[
      BlockHit (disclosureCutoff length leftTape) leftTape value] ≤
      (((9 * 2 ^ 99 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞)) := by
  let cutoff := disclosureCutoff length leftTape
  have hcount : (∑ index : Instance,
      ∏ tree : Tree, (leftDisclosures cutoff leftTape index tree).card) ≤ 9 * 2 ^ 99 := by
    refine le_trans (Finset.sum_le_sum fun index _ => ?_)
      (cutoff_moment_le length leftTape)
    calc
      _ ≤ ∏ _ : Tree, ForsDisclosureTape.loads (blockTape cutoff leftTape) index :=
        Finset.prod_le_prod fun tree _ => ForsDisclosureTape.disclosures_card_le_loads _ index tree
      _ = ForsDisclosureTape.loads (blockTape cutoff leftTape) index ^ 14 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rfl
  have hparse : Pr{let value ← ($ᵗ HashOutput : ProbComp HashOutput)}[
      Covered (leftDisclosures cutoff leftTape) (MessageDigest.parse value)] =
      Pr{let view ← ($ᵗ View : ProbComp View)}[
        Covered (leftDisclosures cutoff leftTape) view] := by
    simpa only [prEvent_map] using (evalDist_parse_uniform.prEvent_eq
      (fun view : View => Covered (leftDisclosures cutoff leftTape) view))
  change Pr{let value ← ($ᵗ HashOutput : ProbComp HashOutput)}[
    Covered (leftDisclosures cutoff leftTape) (MessageDigest.parse value)] ≤ _
  rw [hparse, fresh_coverage]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _

set_option exponentiation.threshold 1024 in
private theorem helped_cutoff_rate (length : Nat) (leftTape : List HashOutput) :
    Pr{let pair ← ($ᵗ (View × View) : ProbComp (View × View))}[
      HelpedBy (leftDisclosures (disclosureCutoff length leftTape) leftTape) pair.1 pair.2] ≤
      1 / ((2 ^ 177 : Nat) : ℝ≥0∞) := by
  exact prob_helpedBy_le_of_moment_cap _ _ (9 * 2 ^ 99)
    (fun part tree => ForsDisclosureTape.disclosures_card_le_loads _ part tree)
    (cutoff_moment_le length leftTape) (by norm_num)

private theorem firedCovered_mono_cutoff {ρ : Type} (len : ρ → Nat)
    (fired : ρ → Nat → Prop) (small large rightLength : Nat) (hcutoff : small ≤ large)
    (outcome : (List HashOutput × List HashOutput) × ρ) :
    FiredCovered len fired small rightLength outcome →
      FiredCovered len fired large rightLength outcome := by
  rintro ⟨target, ht, hr, htrees⟩
  refine ⟨target, ht, hr, fun tree => ?_⟩
  rcases htrees tree with ⟨cell, hcell, hsupply⟩ | hhelper
  · exact Or.inl ⟨cell, lt_of_lt_of_le hcell hcutoff, hsupply⟩
  · exact Or.inr hhelper

private theorem prob_loadMoment_bad_le (length : Nat) (hcap : length ≤ 5 * 2 ^ 62) :
    Pr{let tape ← padding length}[9 * 2 ^ 99 < loadMoment length tape] ≤
      (1 : ℝ≥0∞) / ((8 * 2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hlaw := (evalDist_blockTape length).prEvent_eq
    (fun tape : ForsDisclosureTape.Tape length =>
      9 * 2 ^ 99 < ∑ part, ForsDisclosureTape.loads tape part ^ 14)
  rw [prEvent_map] at hlaw
  change Pr{let tape ← padding length}[
    9 * 2 ^ 99 < ∑ part, ForsDisclosureTape.loads (blockTape length tape) part ^ 14] ≤ _
  rw [hlaw, ForsDisclosureTape.loads_probability
    (fun counts : Instance → Nat => 9 * 2 ^ 99 < ∑ part, counts part ^ 14)]
  convert ForsConcentration.uniform_load_tail_nine_eighths_of_le length hcap using 1
  · congr 1
  · simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

open scoped Classical in
/-- Coverage by the signer cells actually consumed, together with fired targets,
is charged on one fixed full tape law using a left-only analytical disclosure cutoff. -/
theorem prob_usedPrefix_firedCovered_le
    {ρ : Type} (run : List HashOutput → List HashOutput → ProbComp ρ)
    (len : ρ → Nat) (fired : ρ → Nat → Prop)
    (signerCount signerPrefix : ρ → Nat)
    (leftLength rightLength : Nat)
    (hleft : 2 ≤ leftLength) (hcap : leftLength ≤ 5 * 2 ^ 62)
    (hprefix : ∀ outcome ∈ support (blockRunOf run leftLength rightLength),
      signerPrefix outcome.2 ≤ leftLength ∧
        signerPrefix outcome.2 ≤ signerCount outcome.2)
    (hcausal : ∀ (index cell : Nat) (leftTape rightTape : List HashOutput)
        (value : HashOutput), index ≤ cell →
      (Pr{let z ← run leftTape (rightTape.set cell value)}[index < len z]) =
      Pr{let z ← run leftTape rightTape}[index < len z])
    (hthin1 : ∀ (index : Nat) (leftTape rightTape : List HashOutput),
      Pr{let z ← run leftTape rightTape}[index < len z ∧ fired z index] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) *
        Pr{let z ← run leftTape rightTape}[index < len z])
    (hthin2 : ∀ (first second : Nat) (leftTape rightTape : List HashOutput),
      first < second →
      Pr{let z ← run leftTape rightTape}[second < len z ∧ fired z first ∧ fired z second] ≤
      1 / ((2 ^ 256 : Nat) : ℝ≥0∞) *
        Pr{let z ← run leftTape rightTape}[first < len z])
    (hsignerCausal : ∀ (cell : Nat) (leftTape rightTape : List HashOutput)
        (value : HashOutput), 1 ≤ cell →
      (Pr{let z ← run (leftTape.set cell value) rightTape}[2 ≤ signerCount z]) =
      Pr{let z ← run leftTape rightTape}[2 ≤ signerCount z]) :
    Pr{let outcome ← blockRunOf run leftLength rightLength}[
      FiredCovered len fired
        (signerPrefix outcome.2) rightLength outcome] ≤
      ((1 : ℝ≥0∞) / ((8 * 2 ^ 128 : Nat) : ℝ≥0∞)) *
        Pr{let outcome ← blockRunOf run leftLength rightLength}[
          2 ≤ signerCount outcome.2] +
      (∑' outcome,
        Pr{let x ← blockRunOf run leftLength rightLength}[x = outcome] *
          ((len outcome.2 : Nat) : ℝ≥0∞)) *
        ((((9 * 2 ^ 99 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞)) +
          (rightLength : ℝ≥0∞) / ((2 ^ 303 : Nat) : ℝ≥0∞)) := by
  classical
  have hsplit : Pr{let outcome ← blockRunOf run leftLength rightLength}[
        FiredCovered len fired (signerPrefix outcome.2) rightLength outcome] ≤
      Pr{let outcome ← blockRunOf run leftLength rightLength}[
        (9 * 2 ^ 99 < loadMoment leftLength outcome.1.1) ∧ 2 ≤ signerCount outcome.2] +
      Pr{let outcome ← blockRunOf run leftLength rightLength}[
        FiredCovered len fired (disclosureCutoff leftLength outcome.1.1) rightLength outcome] := by
    refine le_trans (prEvent_mono_of_support _ _ _ fun outcome hmem hcovered => ?_)
      (prEvent_or_le _ _ _)
    by_cases hgood : loadMoment leftLength outcome.1.1 ≤ 9 * 2 ^ 99
    · refine Or.inr (firedCovered_mono_cutoff len fired _ _ rightLength ?_ outcome hcovered)
      simpa only [disclosureCutoff, ite_eq_left hgood] using (hprefix outcome hmem).1
    · by_cases hcount : 2 ≤ signerCount outcome.2
      · exact Or.inl ⟨Nat.lt_of_not_ge hgood, hcount⟩
      · refine Or.inr (firedCovered_mono_cutoff len fired _ _ rightLength ?_ outcome hcovered)
        have hp := (hprefix outcome hmem).2
        simp only [disclosureCutoff, ite_eq_right hgood]
        omega
  have hrare : Pr{let outcome ← blockRunOf run leftLength rightLength}[
        (9 * 2 ^ 99 < loadMoment leftLength outcome.1.1) ∧ 2 ≤ signerCount outcome.2] ≤
      ((1 : ℝ≥0∞) / ((8 * 2 ^ 128 : Nat) : ℝ≥0∞)) *
        Pr{let outcome ← blockRunOf run leftLength rightLength}[2 ≤ signerCount outcome.2] := by
    have hlength : leftLength - 1 + 1 = leftLength := by omega
    have hfactor := prEvent_bad_load_and_event_eq_mul run (fun z => 2 ≤ signerCount z)
      (leftLength - 1) rightLength (9 * 2 ^ 99) hsignerCausal
    rw [hlength] at hfactor
    change Pr{let outcome ← blockRunOf run leftLength rightLength}[
      (9 * 2 ^ 99 < ∑ part, ForsDisclosureTape.loads
        (blockTape leftLength outcome.1.1) part ^ 14) ∧ 2 ≤ signerCount outcome.2] ≤ _
    rw [hfactor]
    exact mul_le_mul' (prob_loadMoment_bad_le leftLength hcap) le_rfl
  have hcoverage := prob_firedCovered_and_good_le run len fired leftLength rightLength
    (disclosureCutoff leftLength) (fun _ => True)
    (((9 * 2 ^ 99 : Nat) : ℝ≥0∞) / ((2 ^ 231 : Nat) : ℝ≥0∞))
    (fun leftTape _ => blockHit_cutoff_rate leftLength leftTape)
    (fun leftTape _ => helped_cutoff_rate leftLength leftTape) hcausal hthin1 hthin2
  exact le_trans hsplit (add_le_add hrare (by simpa only [true_and] using hcoverage))

end SLHDSA.SHAKE128s.FiredCoverage
