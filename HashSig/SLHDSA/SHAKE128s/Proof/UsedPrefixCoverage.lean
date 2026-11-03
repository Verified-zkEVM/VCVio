/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.FiredCoverage
public import HashSig.SLHDSA.SHAKE128s.Proof.ForsLoadTail
import VCVio.OracleComp.EvalDist.Sum

/-! # Symmetric load tails and events determined before a second signer answer -/

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

end SLHDSA.SHAKE128s.FiredCoverage

#print axioms SLHDSA.SHAKE128s.FiredCoverage.prEvent_bad_load_and_event_eq_mul
