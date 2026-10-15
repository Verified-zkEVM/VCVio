/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.ResolvedLaws

/-!
# Ranges and lazy comprehension combinators

These derived constructors retain suspended function arguments and sequence
elements. An empty or ignored generator never adds a demand on its source.
Sequential generators allow dependent finite rows; parallel generators admit
finite or infinite sources and truncate at their minimum length. Local matches
use ordinary lexical lets. Infinite inner sequential generators and a general
comprehension AST remain outside this derived interface.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Resolved

/-- A finite integer enumeration with an arbitrary starting integer. -/
@[expose] def Term.range {Γ : List ClosedTy} (start : Int) (n : Nat) :
    Term Γ (.seq (.finite n) .integer) :=
  .sequence n (fun i => .integer (start + (i.val : Int)))

/-- A single-generator comprehension with a suspended element argument. -/
@[expose] def Term.map {Γ : List ClosedTy} {a b : ClosedTy} {l : Length}
    (f : Term Γ (.arrow a b)) (xs : Term Γ (.seq l a)) : Term Γ (.seq l b) :=
  .app (.app (.lam (.lam (.generate l
    (.app (.var (.succ (.succ .zero))) (.index (.var (.succ .zero)) (.var .zero)))))) f) xs

/-- Enumeration exposes precisely the integer assigned to each finite position. -/
theorem denote_range {Γ : List ClosedTy} (start : Int) (n : Nat) (ρ : Environment Γ) :
    denote (Term.range start n) ρ =
      DomainResult.value (fun i : Fin n => DomainResult.value ⟨start + (i.val : Int)⟩) := rfl

/-- Mapping exposes a lazy array even when its function or source is partial. -/
theorem denote_map {Γ : List ClosedTy} {a b : ClosedTy} {l : Length}
    (f : Term Γ (.arrow a b)) (xs : Term Γ (.seq l a)) (ρ : Environment Γ) :
    denote (Term.map f xs) ρ = DomainResult.value (fun i : l.Index =>
      DomainResult.applyContinuous (denote f ρ)
        (Semantics.indexAt (denote xs ρ) (Length.indexNat i))) := rfl

/-- A sequential generator whose finite row may depend on the preceding value.
Rows are visited in source order; a row of length zero never demands its source. -/
@[expose] def Term.flatMap {Γ : List ClosedTy} {a b : ClosedTy} {l : Length}
    (each : Nat) (f : Term Γ (.arrow a (.seq (.finite each) b)))
    (xs : Term Γ (.seq l a)) : Term Γ (.seq (l.mul (.finite each)) b) :=
  .app (.primitive (.join l each b)) (.map f xs)

/-- Sequential generators first select the outer value, then the selected row position.
The equation covers suspended errors and divergence as well as total sequences. -/
theorem denote_flatMap {Γ : List ClosedTy} {a b : ClosedTy} {l : Length}
    (each : Nat) (f : Term Γ (.arrow a (.seq (.finite each) b)))
    (xs : Term Γ (.seq l a)) (ρ : Environment Γ) :
    denote (Term.flatMap each f xs) ρ = Semantics.join l each
      (DomainResult.value (fun i : l.Index => DomainResult.applyContinuous (denote f ρ)
        (Semantics.indexAt (denote xs ρ) (Length.indexNat i)))) := by
  rw [Term.flatMap, denote_app, denote_primitive, Primitive.denote,
    DomainResult.applyContinuous_value, denote_map]

/-- Parallel generators truncate at the shorter length, including infinite sources.
Each selected argument remains suspended until the body demands it. -/
@[expose] def Term.zipWith {Γ : List ClosedTy} {a b c : ClosedTy} {l m : Length}
    (f : Term Γ (.arrow a (.arrow b c)))
    (xs : Term Γ (.seq l a)) (ys : Term Γ (.seq m b)) : Term Γ (.seq (l.min m) c) :=
  .app (.app (.app (.lam (.lam (.lam (.generate (l.min m)
    (.app (.app (.var (.succ (.succ (.succ .zero))))
      (.index (.var (.succ (.succ .zero))) (.var .zero)))
      (.index (.var (.succ .zero)) (.var .zero))))))) f) xs) ys

/-- Parallel generators use the same index without demanding either source in advance. -/
theorem denote_zipWith {Γ : List ClosedTy} {a b c : ClosedTy} {l m : Length}
    (f : Term Γ (.arrow a (.arrow b c)))
    (xs : Term Γ (.seq l a)) (ys : Term Γ (.seq m b)) (ρ : Environment Γ) :
    denote (Term.zipWith f xs ys) ρ = DomainResult.value (fun i : (l.min m).Index =>
      DomainResult.applyContinuous (DomainResult.applyContinuous (denote f ρ)
        (Semantics.indexAt (denote xs ρ) (Length.indexNat i)))
        (Semantics.indexAt (denote ys ρ) (Length.indexNat i))) := by
  simp (config := { dsimp := false }) only [Term.zipWith, denote_app, denote_lam_apply,
    denote_generate, denote_var, denote_index, Environment.extend_succ, Environment.extend_zero]
  rfl

end Interop.Cryptol.Resolved
