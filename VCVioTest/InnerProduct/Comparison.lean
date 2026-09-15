/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.InnerProduct.Replay
public import VCVioTest.InnerProduct.PlainProtocol
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Matched observations of the inner-product prover

The two independently defined source representations agree under every monadic
challenge handler. State, cost, probability, and their combinations are instances
of this one statement. This does not assume or establish an efficient accepting
tree generator in either representation.
-/

public section

namespace InnerProduct.Comparison

variable {F G A : Type} [Field F]

/-- Every handler observes the same source computation at arbitrary depth. -/
theorem run_eq {m : Type → Type} [Monad m] {r : Nat}
    (p : Prover F G r) (finish : Transcript F G r → A) (sample : m Fˣ) :
    simulateQ (fun _ => sample) (source p finish) =
      PlainReplay.run (fun _ => sample) (Plain.source p finish) := by
  induction r generalizing A with
  | zero => rfl
  | succ r ih =>
      change (sample >>= fun x => simulateQ (fun _ => sample)
        (source (p.2 x) (fun tail => finish (.step p.1 x tail)))) =
          (sample >>= fun x => PlainReplay.run (fun _ => sample)
            (Plain.source (p.2 x) (fun tail => finish (.step p.1 x tail))))
      congr 1
      funext x
      exact ih (p.2 x) (fun tail => finish (.step p.1 x tail))

/-- Arbitrary output observations have the same native measure. -/
theorem measure_eq [MeasurableSpace A] {r : Nat}
    (p : Prover F G r) (finish : Transcript F G r → A) (sample : ProbComp Fˣ) :
    𝒟[simulateQ (fun _ => sample) (source p finish)] =
      𝒟[PlainReplay.run (fun _ => sample) (Plain.source p finish)] := by
  rw [run_eq]

/-- Stateful observations, including a work ledger outside the prover's replay
state, have the same joint output/state measure. -/
theorem joint_measure_eq {S : Type} [MeasurableSpace (A × S)] {r : Nat}
    (p : Prover F G r) (finish : Transcript F G r → A)
    (sample : StateT S ProbComp Fˣ) (initial : S) :
    𝒟[(simulateQ (fun _ => sample) (source p finish)).run initial] =
      𝒟[(PlainReplay.run (fun _ => sample) (Plain.source p finish)).run initial] := by
  rw [run_eq]

/-- Any common adaptive consumer of a source runner has exactly the same
behavior in both representations. The consumer may retry, reject, or retain
cost and private state; no output-only erasure is used. -/
theorem consumer_eq {m : Type → Type} [Monad m] {B : Type} {r : Nat}
    (consumer : (Prover F G r → m A) → B)
    (finish : Transcript F G r → A) (sample : m Fˣ) :
    consumer (fun p => simulateQ (fun _ => sample) (source p finish)) =
      consumer (fun p => PlainReplay.run (fun _ => sample) (Plain.source p finish)) := by
  apply congrArg consumer
  funext p
  exact run_eq p finish sample

/-- Sampling a private seed once and then running an adaptive stateful
consumer preserves the entire output/state measure in the comparison.
The state may contain a work ledger that the consumer never rewinds. -/
theorem seeded_consumer_measure_eq {Seed S B : Type} [MeasurableSpace (B × S)]
    {r : Nat} (seed : ProbComp Seed)
    (consumer : Seed → (Prover F G r → StateT S ProbComp A) → StateT S ProbComp B)
    (finish : Transcript F G r → A) (sample : StateT S ProbComp Fˣ) (initial : S) :
    𝒟[do
      let privateSeed ← seed
      (consumer privateSeed (fun p => simulateQ (fun _ => sample) (source p finish))).run initial] =
    𝒟[do
      let privateSeed ← seed
      (consumer privateSeed
        (fun p => PlainReplay.run (fun _ => sample) (Plain.source p finish))).run initial] := by
  simp_rw [consumer_eq]

/-- The nine prescribed leaves agree on the actual public transcript. -/
theorem replay33_output_eq (p : Prover F G 2) (first : Fin 3 → Fˣ)
    (second : Fin 3 → Fin 3 → Fˣ) (i j : Fin 3) :
    PFunctor.FreeM.output (source p id) (replay33Leaf p first second i j).path =
      PlainReplay.output (Plain.source p id) (Plain.replay33Leaf p first second i j).path := rfl

end InnerProduct.Comparison
