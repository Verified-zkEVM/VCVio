/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.InnerProduct.Protocol
public import PolyFun.PFunctor.Free.Cursor.ReplayTree
public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Source executions of the recursive inner-product prover

The private seed is fixed before constructing `Prover`. The only remaining
oracle operation chooses the next public challenge. Each source leaf carries
the complete public transcript, including the messages preceding challenges.
The nine-leaf tree records prescribed branches; finding accepting branches is
a separate probabilistic obligation.
-/

public section

namespace InnerProduct

open PFunctor.FreeM PFunctor.FreeM.Cursor

variable {F G A : Type} [Field F]

/-- One public-challenge oracle. Repeated occurrences denote consecutive rounds. -/
@[expose]
def challengeSpec (F : Type) [Field F] : OracleSpec Unit := fun _ => Fˣ

/-- The actual causal prover as an oracle program. The continuation accumulates
the public transcript without changing the program's challenge occurrences. -/
@[expose]
def source : {r : Nat} → Prover F G r → (Transcript F G r → A) →
    OracleComp (challengeSpec F) A
  | 0, w, finish => pure (finish (.terminal w))
  | _ + 1, ⟨msg, next⟩, finish =>
      .queryBind () fun x => source (next x) (fun tail => finish (.step msg x tail))

/-- The source execution determined by the supplied public challenges. -/
@[expose]
def sourcePath : {r : Nat} → (p : Prover F G r) → (finish : Transcript F G r → A) →
    Challenges Fˣ r → Path (source p finish)
  | 0, _, _, _ => ⟨⟩
  | _ + 1, ⟨_, next⟩, _, ⟨x, xs⟩ => ⟨x, sourcePath (next x) _ xs⟩

/-- A source path returns precisely the transcript of the prescribed execution. -/
theorem source_output {r : Nat} (p : Prover F G r) (finish : Transcript F G r → A)
    (xs : Challenges Fˣ r) :
    output (source p finish) (sourcePath p finish xs) = finish (respond p xs) := by
  induction r generalizing A with
  | zero => rfl
  | succ r ih => exact ih (p.2 xs.1) (fun tail => finish (.step p.1 xs.1 tail)) xs.2

/-- Public challenge events in execution order. -/
@[expose]
def challengeEvents : {r : Nat} → Challenges Fˣ r → List ((challengeSpec F).toPFunctor.Idx)
  | 0, _ => []
  | _ + 1, ⟨x, xs⟩ => ⟨(), x⟩ :: challengeEvents xs

/-- Trace observation agrees with the prescribed public challenges. -/
theorem source_trace {r : Nat} (p : Prover F G r) (finish : Transcript F G r → A)
    (xs : Challenges Fˣ r) :
    Path.trace (source p finish) (sourcePath p finish xs) = challengeEvents xs := by
  induction r generalizing A with
  | zero => rfl
  | succ r ih =>
      exact congrArg (List.cons _)
        (ih (p.2 xs.1) (fun tail => finish (.step p.1 xs.1 tail)) xs.2)

/-- A completed source execution makes exactly one challenge query per round. -/
theorem source_query_count {r : Nat} (p : Prover F G r) (finish : Transcript F G r → A)
    (xs : Challenges Fˣ r) :
    (Path.trace (source p finish) (sourcePath p finish xs)).length = r := by
  rw [source_trace]
  induction r with
  | zero => rfl
  | succ r ih =>
      exact congrArg (· + 1)
        (ih (p.2 xs.1) (fun tail => finish (.step p.1 xs.1 tail)) xs.2)

/-- Every source execution, not just a chosen replay schedule, makes exactly
one public-challenge query per remaining round. -/
theorem source_query_count_all {r : Nat} (p : Prover F G r)
    (finish : Transcript F G r → A) (path : Path (source p finish)) :
    (Path.trace (source p finish) path).length = r := by
  induction r generalizing A with
  | zero => rfl
  | succ r ih =>
      exact congrArg (· + 1)
        (ih (p.2 path.1) (fun tail => finish (.step p.1 path.1 tail)) path.2)

/-- Nine prescribed executions with three branches at each of two rounds. -/
@[expose]
def replay33 (p : Prover F G 2) (first : Fin 3 → Fˣ)
    (second : Fin 3 → Fin 3 → Fˣ) : ReplayTree (source p id) :=
  .branch (.here _) 3 first fun i =>
    .branch (.here _) 3 (second i) fun _j => .leaf ⟨⟩

/-- Select one of the nine prescribed executions. -/
@[expose]
def replay33Leaf (p : Prover F G 2) (first : Fin 3 → Fˣ)
    (second : Fin 3 → Fin 3 → Fˣ) (i j : Fin 3) :
    ReplayTree.Leaf (replay33 p first second) := .branch i (.branch j .leaf)

/-- The selected replay leaf is an execution of the original seeded prover. -/
theorem replay33_path (p : Prover F G 2) (first : Fin 3 → Fˣ)
    (second : Fin 3 → Fin 3 → Fˣ) (i j : Fin 3) :
    (replay33Leaf p first second i j).path =
      sourcePath p id (first i, second i j, ()) := rfl

/-- Public transcripts at replay leaves are the actual prover transcripts. -/
theorem replay33_output (p : Prover F G 2) (first : Fin 3 → Fˣ)
    (second : Fin 3 → Fin 3 → Fˣ) (i j : Fin 3) :
    output (source p id) (replay33Leaf p first second i j).path =
      respond p (first i, second i j, ()) := rfl

end InnerProduct
