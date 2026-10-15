/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyRecursion
public import Interop.Cryptol.Model.PolyRenaming
public import Interop.Cryptol.Model.PolySubstitutionSemantics
public import Interop.Cryptol.Translation.PolymorphicExamples
public import PolyFun.IPFunctor.Scoped.FamilySize

/-! # Ordered stages, binding positions, finite descriptions and certificates -/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Tests.OrderedPolymorphic

open Polymorphic

/-- Two explicit instantiation stages. -/
@[expose] def stages : Scheme 0 0 := .allNum (.allType (.mono .bit))

private def early : Term Scope.empty [] stages := .error _ (.user "stage")

/-- Fail after the numeric stage. -/
@[expose] def middle : Term Scope.empty [] stages := .numAbs (.error _ (.user "stage"))

/-- Fail after both numeric and type stages. -/
@[expose] def late : Term Scope.empty [] stages := .numAbs (.typeAbs (.error _ (.user "stage")))

example : early.denote emptyAssignment (Env.empty _) = DomainResult.error (.user "stage") := rfl

example : middle.denote emptyAssignment (Env.empty _) =
    DomainResult.value (fun _ : Length =>
      (DomainResult.error (.user "stage") :
        DomainResult EvalError (ClosedTy → Computation .bit))) :=
  rfl

example : late.denote emptyAssignment (Env.empty _) =
    DomainResult.value (fun _ : Length => DomainResult.value
      (fun _ : ClosedTy => (DomainResult.error (.user "stage") : Computation .bit))) := rfl

/-- Each explicit quantifier preserves its own demand boundary. -/
theorem stages_distinct : middle.denote emptyAssignment (Env.empty _) ≠
    late.denote emptyAssignment (Env.empty _) := by
  intro h
  have he := congrFun (DomainResult.value_inj.mp h) (.finite 0)
  exact DomainResult.value_ne_error _ _ he.symm

private abbrev trivialConstraint : Constraint 0 := .eq (.finite 0) (.finite 0)

private def guarded : Term Scope.empty [] (.guard trivialConstraint (.allNum (.mono .bit))) :=
  Term.proofAbs (w := Scope.empty) trivialConstraint (.error _ (.user "guard"))

example : guarded.denote emptyAssignment (Env.empty _) ⟨rfl⟩ =
    DomainResult.error (.user "guard") := rfl

private abbrev twoTypes : Scope := ⟨0, 2, []⟩

private def mergeTypes : Scope.Map twoTypes Scope.empty :=
  ⟨⟨Fin.elim0, fun _ => .bit⟩, fun _ _ h => nomatch h⟩

private abbrev separate : List twoTypes.ValueSort := [.mono (.var 0), .mono (.var 1)]

private def first : Term twoTypes separate (.mono (.var 0)) := .var .zero

private def second : Term twoTypes separate (.mono (.var 1)) := .var (.succ .zero)

example : first.parameters mergeTypes =
    (Term.var .zero : Term Scope.empty [.mono .bit, .mono .bit] (.mono .bit)) := rfl

example : second.parameters mergeTypes =
    (Term.var (.succ .zero) : Term Scope.empty [.mono .bit, .mono .bit] (.mono .bit)) := rfl

example : first.parameters mergeTypes ≠ second.parameters mergeTypes := by
  intro h
  cases h

private def capture : Term Scope.empty [.mono .bit]
    (.allType (.mono (.arrow (.var 0) .bit))) :=
  .typeAbs (.lam (.var (.succ .zero)))

private def replaceBit : signature.Substitution (w := Scope.empty) [.mono .bit] []
  | _, .zero => Term.bit true
  | _, .succ x => nomatch x

example (a : ClosedTy) (x : Computation a) :
    DomainResult.applyContinuous ((capture.subst replaceBit).observe emptyAssignment
      (.type a (.mono (.arrow (.var 0) .bit) _)) (Env.empty _)) x =
        DomainResult.value ⟨true⟩ := rfl

private def localIdentity : Term Scope.empty []
    (.allType (.mono (.arrow (.var 0) (.var 0)))) := .typeAbs (.lam (.var .zero))

private def twoUses : Term Scope.empty [] (.mono (.prod .bit .integer)) :=
  .letE localIdentity
    (.pair (.app (.typeApp (.var .zero) .bit) (.bit true))
      (.app (.typeApp (.var .zero) .integer) (.integer 3)))

example : twoUses.denote emptyAssignment (Env.empty _) =
    DomainResult.value (DomainResult.value ⟨true⟩, DomainResult.value ⟨(3 : Int)⟩) := rfl

example : IPFunctor.ScopedFamily.Term.nodeCount Polymorphic.Examples.map = 11 := by decide

example : IPFunctor.ScopedFamily.Term.nodeCount Polymorphic.Examples.xor = 10 := by decide

example : IPFunctor.ScopedFamily.Term.nodeCount Polymorphic.Examples.shiftedCycle = 4 := by decide

example : Polymorphic.Examples.shiftedCycle.denote emptyAssignment (Env.empty _) ≠ ⊥ := by
  rw [Polymorphic.Examples.shiftedCycle_partial]
  exact DomainResult.value_ne_bot _

example (n : Nat) (x y : BitVec n) :
    DomainResult.applyContinuous
      (Finite.PolymorphicExamples.xorCertificate.meaningAt n).meaning
      (Finite.encodeData (.prod (.word n) (.word n)) (x, y)) =
        Finite.encodeData (.word n) (x ^^^ y) :=
  Finite.PolymorphicExamples.xorCertificate.correct n (x, y)

example : (Finite.PolymorphicExamples.xorCertificate.meaningAt 0).implementation
    ((0 : BitVec 0), (0 : BitVec 0)) = (0 : BitVec 0) := rfl

/-- Renaming an open recursive group retains one simultaneous fixed point. -/
example {w : Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (bindings : List w.ValueSort)
    (rhs : (i : Fin bindings.length) → Term w (bindings ++ Γ) bindings[i])
    (body : Term w (bindings ++ Γ) s) (r : IPFunctor.ScopedSignature.Renaming Γ Δ)
    (ρ : w.Assignment) (η : Env ρ Δ) :
    Term.denote ((Term.letRec bindings rhs body).rename r) ρ η =
      (Term.letRec bindings rhs body).denote ρ (Env.rename ρ r η) :=
  Term.denote_rename _ r ρ η

/-- The general theorem also covers empty declaration groups. -/
example {w : Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (body : Term w Γ s) (r : IPFunctor.ScopedSignature.Renaming Γ Δ)
    (ρ : w.Assignment) (η : Env ρ Δ) :
    Term.denote ((Term.letRec [] (fun i => Fin.elim0 i) body).rename r) ρ η =
      (Term.letRec [] (fun i => Fin.elim0 i) body).denote ρ (Env.rename ρ r η) :=
  Term.denote_rename _ r ρ η

/-- Result annotations may use an arbitrary equality between different schemes. -/
example {w : Scope} {s t : w.ValueSort} (e : s = t) (op : Op w s) :
    HEq ((Head.mk ⟨s, op⟩ e).map (Scope.Map.id w)) (Head.mk ⟨s, op⟩ e) :=
  Head.map_id_heq _

/-- Head fusion permits different scopes and noninjective symbolic substitutions. -/
example {w z u : Scope} (μ : Scope.Map w z) (ν : Scope.Map z u)
    {s : w.ValueSort} (h : Head w s) :
    HEq ((h.map μ).map ν) (h.map (μ.comp ν)) := Head.map_map_heq μ ν h

/-- Collapsing type parameters retains distinct error and value positions. -/
example :
    let ρ := emptyAssignment
    let η : Env (mergeTypes.pull ρ) separate :=
      Env.cons _ (Env.cons _ (Env.empty _, DomainResult.value ⟨true⟩),
        DomainResult.error (.user "first"))
    (Term.parameters mergeTypes (.pair first second)).denote ρ
      (Env.parameters mergeTypes ρ η) =
        DomainResult.value (DomainResult.error (.user "first"), DomainResult.value ⟨true⟩) := by
  dsimp only
  exact eq_of_heq (Term.denote_parameters_related (.pair first second) mergeTypes
    emptyAssignment (mergeTypes.pull emptyAssignment) rfl _ _
    (Env.parameters_related mergeTypes emptyAssignment _))

private def mixed : Term Scope.empty [.mono .bit]
    (.allNum (.allType (.guard (.eq (.finite 0) (.finite 0)) (.mono .bit)))) :=
  .numAbs (.typeAbs (.proofAbs (.eq (.finite 0) (.finite 0)) (.var .zero)))

/-- Partial images remain suspended beneath numeric, type and erased proof binders. -/
example {Δ : List Scope.empty.ValueSort}
    (θ : signature.Substitution (w := Scope.empty) [.mono .bit] Δ)
    (η : Env emptyAssignment Δ) :
    (mixed.subst θ).denote emptyAssignment η =
      DomainResult.value (fun _ : Length => DomainResult.value (fun _ : ClosedTy =>
        fun _ : PLift ((Constraint.eq (.finite 0) (.finite 0)).Holds Fin.elim0) =>
          Term.denote (θ .zero) emptyAssignment η)) := by
  rw [Term.denote_subst]
  rfl

/-- Two substitutions preserve capture avoidance below a type binder on partial environments. -/
example {Δ Θ : List Scope.empty.ValueSort}
    (θ : signature.Substitution (w := Scope.empty) [.mono .bit] Δ)
    (τ : signature.Substitution Δ Θ) (η : Env emptyAssignment Θ) :
    ((capture.subst θ).subst τ).denote emptyAssignment η =
      capture.denote emptyAssignment
        (Env.substitute emptyAssignment θ (Env.substitute emptyAssignment τ η)) := by
  rw [Term.denote_subst, Term.denote_subst]

/-- Parameter identity is available as a single simplifier call through ordinary imports. -/
example {w : Scope} {Γ : List w.ValueSort} {s : w.ValueSort} (t : Term w Γ s) :
    HEq (Term.parameters (Scope.Map.id w) t) t := by simp

/-- Fusion applies to arbitrary checked result annotations and context transports. -/
example {w z u : Scope} {Γ Δ : List w.ValueSort} {a b : w.ValueSort}
    (t : Term w Γ a) (hΓ : Γ = Δ) (hab : a = b) (μ : Scope.Map w z) (ν : Scope.Map z u) :
    HEq (Term.parameters ν (Term.parameters μ (t.cast hΓ hab)))
      (Term.parameters (μ.comp ν) (t.cast hΓ hab)) :=
  Term.parameters_parameters_heq μ ν _

/-- Value substitution is associative on descriptions with arbitrary annotations. -/
example {w : Scope} {Γ Δ Θ : List w.ValueSort} {a b : w.ValueSort}
    (t : Term w Γ a) (hab : a = b) (θ : signature.Substitution Γ Δ)
    (τ : signature.Substitution Δ Θ) :
    Term.subst τ (Term.subst θ (t.cast rfl hab)) =
      Term.subst (fun x => Term.subst τ (θ x)) (t.cast rfl hab) :=
  Term.subst_subst _ θ τ

/-- Parameter/value fusion permits noninjective maps and arbitrary substitution images. -/
example {Δ : List twoTypes.ValueSort} {s : twoTypes.ValueSort}
    (t : Term twoTypes separate s) (θ : signature.Substitution separate Δ) :
    Term.parameters mergeTypes (t.subst θ) =
      (Term.parameters mergeTypes t).subst (θ.map parameterHom mergeTypes) :=
  Term.parameters_subst mergeTypes θ t

/-- Semantic substitution acts on a whole recursive group, with no totality premise. -/
example {w : Scope} {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (bindings : List w.ValueSort)
    (rhs : (i : Fin bindings.length) → Term w (bindings ++ Γ) bindings[i])
    (body : Term w (bindings ++ Γ) s) (θ : signature.Substitution Γ Δ)
    (ρ : w.Assignment) (η : Env ρ Δ) :
    Term.denote ((Term.letRec bindings rhs body).subst θ) ρ η =
      (Term.letRec bindings rhs body).denote ρ (Env.substitute ρ θ η) :=
  Term.denote_subst _ θ ρ η

/-- Recursive calls at changed instantiations remain partial after parameter mapping. -/
example :
    HEq (Term.denote (Term.parameters (Scope.Map.id Scope.empty)
      Polymorphic.Examples.shiftedCycle) emptyAssignment (Env.empty _))
      (Polymorphic.Examples.shiftedCycle.denote emptyAssignment (Env.empty _)) := by
  apply Term.denote_parameters_related
  · exact (ParameterAssignment.pull_id emptyAssignment.val).symm
  · intro a b x
    nomatch x

end Interop.Cryptol.Tests.OrderedPolymorphic
