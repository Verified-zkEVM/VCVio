/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.InnerProduct.Protocol
public import VCVioTest.InnerProduct.PlainReplay

/-!
# The published protocol on ordinary dependent effects

The protocol's algebra and causal prover interface are shared with the library
implementation. This module imports no PolyFun or VCVio production module.
All reconstruction results are parametric in the folding depth.
-/

public section

namespace InnerProduct.Plain

variable {F G A : Type} [Field F]

/-- The causal protocol in independent request/continuation syntax. -/
@[expose]
def source : {r : Nat} → Prover F G r → (Transcript F G r → A) →
    PlainReplay.Program Unit (fun _ => Fˣ) A
  | 0, w, finish => .ret (finish (.terminal w))
  | _ + 1, ⟨msg, next⟩, finish =>
      .call () fun x => source (next x) (fun tail => finish (.step msg x tail))

/-- An ordinary dependent path for prescribed public challenges. -/
@[expose]
def sourcePath : {r : Nat} → (p : Prover F G r) → (finish : Transcript F G r → A) →
    Challenges Fˣ r → PlainReplay.Path (source p finish)
  | 0, _, _, _ => ⟨⟩
  | _ + 1, ⟨_, next⟩, _, ⟨x, xs⟩ => ⟨x, sourcePath (next x) _ xs⟩

/-- Ordinary effects return the same prescribed prover transcript. -/
theorem source_output {r : Nat} (p : Prover F G r) (finish : Transcript F G r → A)
    (xs : Challenges Fˣ r) :
    PlainReplay.output (source p finish) (sourcePath p finish xs) = finish (respond p xs) := by
  induction r generalizing A with
  | zero => rfl
  | succ r ih => exact ih (p.2 xs.1) (fun tail => finish (.step p.1 xs.1 tail)) xs.2

/-- Every ordinary source execution has the same exact public-query count. -/
theorem source_query_count_all {r : Nat} (p : Prover F G r)
    (finish : Transcript F G r → A) (path : PlainReplay.Path (source p finish)) :
    (PlainReplay.trace (source p finish) path).length = r := by
  induction r generalizing A with
  | zero => rfl
  | succ r ih =>
      exact congrArg (· + 1)
        (ih (p.2 path.1) (fun tail => finish (.step p.1 path.1 tail)) path.2)

/-- Prescribed two-round branching on independent saved continuations. -/
@[expose]
def replay33 (p : Prover F G 2) (first : Fin 3 → Fˣ)
    (second : Fin 3 → Fin 3 → Fˣ) : PlainReplay.Tree (source p id) :=
  .branch (.root _) 3 first fun i =>
    .branch (.root _) 3 (second i) fun _j => .leaf ⟨⟩

/-- Select an ordinary replay leaf. -/
@[expose]
def replay33Leaf (p : Prover F G 2) (first : Fin 3 → Fˣ)
    (second : Fin 3 → Fin 3 → Fˣ) (i j : Fin 3) :
    PlainReplay.Leaf (replay33 p first second) := .branch i (.branch j .leaf)

/-- An ordinary replay leaf reconstructs the actual source transcript. -/
theorem replay33_output (p : Prover F G 2) (first : Fin 3 → Fˣ)
    (second : Fin 3 → Fin 3 → Fˣ) (i j : Fin 3) :
    PlainReplay.output (source p id) (replay33Leaf p first second i j).path =
      respond p (first i, second i j, ()) := rfl

end InnerProduct.Plain
