/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.Compression
public import Interop.Cryptol.Bridge.SourceFoundation
public import PolyFunCryptol.Model.Recurrence
public import PolyFunCryptol.Translation.DataCertificate

/-!
# Partial semantics of the preserved compression source

The schedule remains a least fixed point and the round loop remains a lazy
finite fold. The source equation applies to arbitrary suspended inputs;
totality is established separately for represented blocks and states.
-/

public section

open OmegaCompletePartialOrder

namespace Cryptol.Bridge

open Cryptol

/-- The partial word carrier of the instantiated source. -/
abbrev PartialWord := Computation (wordTy 32)

/-- The partial state carrier, with eight suspended words. -/
abbrev PartialState := Computation (.seq (.finite 8) (wordTy 32))

/-- A partial 64-word schedule. -/
abbrev PartialSchedule := Computation (.seq (.finite 64) (wordTy 32))

/-- A partial 16-word message block. -/
abbrev PartialBlock := Computation (.seq (.finite 16) (wordTy 32))

/-- Three source shifts combined by the two source XORs. -/
@[expose] noncomputable def sigmaMeaning (a b c : Nat) (third : ShiftOp) :
    PartialWord →𝒄 PartialWord :=
  .ofFun (fun x => Semantics.wordLogic 32 .xor
    (Semantics.wordLogic 32 .xor
      (Semantics.shift .rotateRight 32 x (.value ⟨(a : Int)⟩))
      (Semantics.shift .rotateRight 32 x (.value ⟨(b : Int)⟩)))
    (Semantics.shift third 32 x (.value ⟨(c : Int)⟩)))

/-- The tupled choice function retains suspended projections of its input. -/
@[expose] noncomputable def choiceTupleMeaning :
    Computation (.prod (wordTy 32) (.prod (wordTy 32) (wordTy 32))) →𝒄 PartialWord :=
  .ofFun (fun p =>
    let x := DomainResult.bind (.ofFun Prod.fst) p
    let yz := DomainResult.bind (.ofFun Prod.snd) p
    let y := DomainResult.bind (.ofFun Prod.fst) yz
    let z := DomainResult.bind (.ofFun Prod.snd) yz
    Semantics.wordLogic 32 .xor (Semantics.wordLogic 32 .and x y)
      (Semantics.wordLogic 32 .and (Semantics.wordNot 32 x) z))

/-- The tupled majority function retains suspended projections of its input. -/
@[expose] noncomputable def majorityTupleMeaning :
    Computation (.prod (wordTy 32) (.prod (wordTy 32) (wordTy 32))) →𝒄 PartialWord :=
  .ofFun (fun p =>
    let x := DomainResult.bind (.ofFun Prod.fst) p
    let yz := DomainResult.bind (.ofFun Prod.snd) p
    let y := DomainResult.bind (.ofFun Prod.fst) yz
    let z := DomainResult.bind (.ofFun Prod.snd) yz
    Semantics.wordLogic 32 .xor
      (Semantics.wordLogic 32 .xor (Semantics.wordLogic 32 .and x y)
        (Semantics.wordLogic 32 .and x z)) (Semantics.wordLogic 32 .and y z))

/-- The source generator's element equations, before solving recursion. -/
@[expose] noncomputable def scheduleMeaningBody (m : PartialBlock) :
    PartialSchedule →𝒄 (Fin 64 → PartialWord) :=
  .ofFun (fun w i => if i.val ≤ 15 then Semantics.indexAt m i.val else
    Semantics.wordArithmetic 32 .add
      (Semantics.wordArithmetic 32 .add
        (Semantics.wordArithmetic 32 .add
          (sigmaMeaning 17 19 10 .right (Semantics.indexAt w ((i.val : Int) - 2)))
          (Semantics.indexAt w ((i.val : Int) - 7)))
        (sigmaMeaning 7 18 3 .right (Semantics.indexAt w ((i.val : Int) - 15))))
      (Semantics.indexAt w ((i.val : Int) - 16)))

/-- The source recursive schedule has the lifted-array least-fixed-point meaning. -/
@[expose] noncomputable def scheduleMeaning (m : PartialBlock) : PartialSchedule :=
  (DomainResult.generateStep (scheduleMeaningBody m)).fix

/-- The resolved constants as a complete but lazily represented table. -/
@[expose] noncomputable def constantsMeaning : PartialSchedule :=
  .value (fun i => .value (wordValue (Foundation.constants256 i)))

@[fun_prop] private theorem vecCons_continuous {A D : Type}
    [OmegaCompletePartialOrder A] [OmegaCompletePartialOrder D] {n : Nat}
    (f : A → D) (g : A → Fin n → D) (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous (fun x => Matrix.vecCons (f x) (g x)) := by
  apply ωScottContinuous.of_apply₂
  intro i
  refine Fin.cases hf (fun j => ?_) i
  change ωScottContinuous (fun x => g x j)
  fun_prop

set_option maxRecDepth 2048 in
/-- The source round retains partial registers, schedule entries, and integer indices. -/
@[expose] noncomputable def roundMeaning (w : PartialSchedule) :
    PartialState →𝒄 (Computation .integer →𝒄 PartialState) :=
  .ofFun (fun s => .ofFun (fun t =>
    let a := Semantics.indexAt s 0
    let b := Semantics.indexAt s 1
    let c := Semantics.indexAt s 2
    let d := Semantics.indexAt s 3
    let e := Semantics.indexAt s 4
    let f := Semantics.indexAt s 5
    let g := Semantics.indexAt s 6
    let h := Semantics.indexAt s 7
    let ch := Semantics.wordLogic 32 .xor (Semantics.wordLogic 32 .and e f)
      (Semantics.wordLogic 32 .and (Semantics.wordNot 32 e) g)
    let maj := Semantics.wordLogic 32 .xor
      (Semantics.wordLogic 32 .xor (Semantics.wordLogic 32 .and a b)
        (Semantics.wordLogic 32 .and a c)) (Semantics.wordLogic 32 .and b c)
    let t1 := Semantics.wordArithmetic 32 .add
      (Semantics.wordArithmetic 32 .add
        (Semantics.wordArithmetic 32 .add
          (Semantics.wordArithmetic 32 .add h (sigmaMeaning 6 11 25 .rotateRight e)) ch)
        (Semantics.index constantsMeaning t)) (Semantics.index w t)
    let t2 := Semantics.wordArithmetic 32 .add (sigmaMeaning 2 13 22 .rotateRight a) maj
    DomainResult.valueContinuous
      ![Semantics.wordArithmetic 32 .add t1 t2, a, b, c,
        Semantics.wordArithmetic 32 .add d t1, e, f, g]))

/-- The source range `[0 ..< 64]`, retaining integer rather than word indices. -/
@[expose] noncomputable def roundIndices : Computation (.seq (.finite 64) .integer) :=
  .value (fun i => .value ⟨(i.val : Int)⟩)

/-- Source compression: recursive schedule, lazy finite fold, and aggregate feed-forward. -/
@[expose] noncomputable def compressionMeaning (s : PartialState) (m : PartialBlock) :
    PartialState :=
  Semantics.wordArrayArithmetic 8 32 .add s
    (Semantics.foldlPrefix 64 64 (Semantics.function₂ (roundMeaning (scheduleMeaning m)))
      s roundIndices)

end Cryptol.Bridge
