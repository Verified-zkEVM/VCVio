/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolySpecialization
public import Interop.Cryptol.Model.PolySubstitution

/-!
# Finite polymorphic map and word functions

The descriptions are built once, with symbolic parameters and explicit ordered
abstractions. Their specializations choose meanings; they do not construct new
source trees indexed by a host-language function.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Polymorphic

/-- The unique valid assignment of a closed parameter scope. -/
@[expose] def emptyAssignment : Scope.empty.Assignment :=
  ⟨⟨Fin.elim0, Fin.elim0⟩, fun _ h => nomatch h⟩

namespace Examples

/-- The body type of length- and type-polymorphic map, after its three binders. -/
@[expose, reducible] def mapType : PolyTy 1 2 :=
  .arrow (.arrow (.var 1) (.var 0)) (.arrow (.seq (.var 0) (.var 1)) (.seq (.var 0) (.var 0)))

/-- Ordered numeric, input-type and output-type quantification. -/
@[expose, reducible] def mapScheme : Scheme 0 0 :=
  .allNum (.allType (.allType (.mono mapType)))

/-- One finite source for lazy map, including infinite input sequences. -/
@[expose] def map : Term Scope.empty [] mapScheme :=
  .numAbs (.typeAbs (.typeAbs (.lam (.lam (.generate (.var 0)
    (.app (.var (.succ (.succ .zero))) (.index (.var (.succ .zero)) (.var .zero))))))))

/-- Checked ordered specialization of map. -/
@[expose] def mapInstance (l : Length) (a b : ClosedTy) :
    Specialization mapScheme emptyAssignment.val
      (.arrow (.arrow a b) (.arrow (.seq l a) (.seq l b))) :=
  .num l (.type a (.type b (.mono mapType _)))

/-- A specialization preserves map's lazy indexing behavior for arbitrary partial inputs. -/
theorem map_apply_suspended (l : Length) (a b : ClosedTy) (f : Computation (.arrow a b))
    (xs : Computation (.seq l a)) :
    DomainResult.applyContinuous
      (DomainResult.applyContinuous (map.observe emptyAssignment (mapInstance l a b)
        (Env.empty _)) f) xs =
      DomainResult.value (fun i : l.Index => DomainResult.applyContinuous
        f (Semantics.index xs (DomainResult.value ⟨(Length.indexNat i : Int)⟩))) := rfl

/-- With an available function, mapping an element passes the selected suspended input. -/
theorem map_apply (l : Length) (a b : ClosedTy) (f : Computation a →𝒄 Computation b)
    (xs : Computation (.seq l a)) :
    DomainResult.applyContinuous
      (DomainResult.applyContinuous (map.observe emptyAssignment (mapInstance l a b)
        (Env.empty _)) (DomainResult.value f)) xs =
      DomainResult.value (fun i : l.Index =>
        f (Semantics.index xs (DomainResult.value ⟨(Length.indexNat i : Int)⟩))) := rfl

/-- A width-polymorphic XOR consumes a tuple of two words. -/
@[expose, reducible] def xorType : PolyTy 1 0 :=
  .arrow (.prod (.seq (.var 0) .bit) (.seq (.var 0) .bit)) (.seq (.var 0) .bit)

/-- Finite widths are explicit assumptions; zero width is admitted. -/
@[expose, reducible] def xorScheme : Scheme 0 0 :=
  .allNum (.guard (.fin (.var 0)) (.mono xorType))

/-- One finite description of XOR for all finite widths. -/
@[expose] def xor : Term Scope.empty [] xorScheme :=
  .numAbs (.proofAbs (.fin (.var 0)) (.lam
    (.app (.app (.wordLogic (.var 0) .xor (Scope.entails_here _ _))
      (.fst (.var .zero))) (.snd (.var .zero)))))

/-- A checked specialization at any finite width, including zero. -/
@[expose] def xorInstance (n : Nat) : Specialization xorScheme emptyAssignment.val
    (.arrow (.prod (wordTy n) (wordTy n)) (wordTy n)) :=
  .num (.finite n) (.proof (.fin (.var 0)) ⟨n, rfl⟩ (.mono xorType _))

end Examples
end Interop.Cryptol.Polymorphic
