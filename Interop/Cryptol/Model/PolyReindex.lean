/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolySyntax
public import Interop.Cryptol.Model.PolyScopeMaps
public import PolyFun.IPFunctor.Scoped.FamilyMap

/-!
# Symbolic parameter substitution in finite descriptions

Constructor heads translate structurally. Checked result annotations absorb
scheme equations, and the PolyFun traversal lifts the substitution at binders.
Variable positions survive noninjective substitutions unchanged.
-/

public section

namespace Interop.Cryptol.Polymorphic

theorem apply_quoteType_subst {n v m u : Nat} (μ : ParameterSubstitution n v m u)
    (a : ClosedTy) : μ.apply (quoteType n v a) = quoteType m u a := by
  induction a with
  | var x => exact x.elim
  | bit | integer | unit => rfl
  | seq l a ih => cases l <;> simp_all [quoteType, ParameterSubstitution.apply,
      Ty.instantiate, NumExpr.subst]
  | prod a b iha ihb | arrow a b iha ihb =>
      simp_all [quoteType, ParameterSubstitution.apply, Ty.instantiate]

namespace Op

/-- Translate constructor data before checking its result annotation. -/
@[expose] def mapHead {w z : Scope} (μ : Scope.Map w z) :
    {s : w.ValueSort} → Op w s → (t : z.ValueSort) × Op z t
  | _, .numAbs s => ⟨_, .numAbs (s.subst μ.parameters.liftNum)⟩
  | _, .numApp s a => ⟨_, .numApp (s.subst μ.parameters.liftNum) (a.subst μ.parameters.numbers)⟩
  | _, .typeAbs s => ⟨_, .typeAbs (s.subst μ.parameters.liftType)⟩
  | _, .typeApp s a => ⟨_, .typeApp (s.subst μ.parameters.liftType) (μ.parameters.apply a)⟩
  | _, .proofAbs c s => ⟨_, .proofAbs (c.subst μ.parameters.numbers) (μ.sort s)⟩
  | _, .proofApp c s h => ⟨_, .proofApp (c.subst μ.parameters.numbers) (μ.sort s) (μ.entails h)⟩
  | _, .bit b => ⟨_, .bit b⟩
  | _, .integer i => ⟨_, .integer i⟩
  | _, .unit => ⟨_, .unit⟩
  | _, .error s e => ⟨_, .error (μ.sort s) e⟩
  | _, .lam a b => ⟨_, .lam (μ.parameters.apply a) (μ.parameters.apply b)⟩
  | _, .app a b => ⟨_, .app (μ.parameters.apply a) (μ.parameters.apply b)⟩
  | _, .letE s t => ⟨_, .letE (μ.sort s) (μ.sort t)⟩
  | _, .pair a b => ⟨_, .pair (μ.parameters.apply a) (μ.parameters.apply b)⟩
  | _, .fst a b => ⟨_, .fst (μ.parameters.apply a) (μ.parameters.apply b)⟩
  | _, .snd a b => ⟨_, .snd (μ.parameters.apply a) (μ.parameters.apply b)⟩
  | _, .generate l a => ⟨_, .generate (l.subst μ.parameters.numbers) (μ.parameters.apply a)⟩
  | _, .index l a => ⟨_, .index (l.subst μ.parameters.numbers) (μ.parameters.apply a)⟩
  | _, .ite s => ⟨_, .ite (μ.sort s)⟩
  | _, .fix s => ⟨_, .fix (μ.sort s)⟩
  | _, .letRec bindings s => ⟨_, .letRec (bindings.map μ.sort) (μ.sort s)⟩
  | _, .bitNot => ⟨_, .bitNot⟩
  | _, .bitOp op => ⟨_, .bitOp op⟩
  | _, .intOp op => ⟨_, .intOp op⟩
  | _, .intEq => ⟨_, .intEq⟩
  | _, .intLt => ⟨_, .intLt⟩
  | _, .wordLogic l op h => ⟨_, .wordLogic (l.subst μ.parameters.numbers) op (μ.entails h)⟩
  | _, .closed t => ⟨_, .closed t⟩

/-- The translated constructor's computed result is the substituted scheme. -/
theorem mapHead_result {w z : Scope} (μ : Scope.Map w z) {s : w.ValueSort} (op : Op w s) :
    (op.mapHead μ).1 = μ.sort s := by
  cases op <;> try rfl
  · simp only [mapHead, Scope.Map.sort, Scheme.subst_subst, ParameterSubstitution.singleNum_comp]
  · simp only [mapHead, Scope.Map.sort, Scheme.subst_subst, ParameterSubstitution.singleType_comp]
  · simp only [mapHead, Scope.Map.sort, Scheme.subst, apply_quoteType_subst]

/-- Parameter substitution preserves the finite list of recursive positions. -/
@[simp] theorem mapHead_arity {w z : Scope} (μ : Scope.Map w z) {s : w.ValueSort}
    (op : Op w s) : (op.mapHead μ).2.arity = op.arity := by
  cases op <;> simp only [mapHead, arity, List.length_map]

/-- Lift the checked substitution into a particular child. -/
@[expose] def childMap {w z : Scope} (μ : Scope.Map w z) {s : w.ValueSort}
    (op : Op w s) (p : Fin (op.mapHead μ).2.arity) :
    Scope.Map (op.world (p.cast (op.mapHead_arity μ))) ((op.mapHead μ).2.world p) := by
  cases op <;> first | exact μ.liftNum | exact μ.liftType | exact μ.assume _ | exact μ

theorem childMap_reindex {w z : Scope} (μ : Scope.Map w z) {s : w.ValueSort}
    (op : Op w s) (p : Fin (op.mapHead μ).2.arity) (a : w.ValueSort) :
    (op.childMap μ p).sort (op.reindex (p.cast (op.mapHead_arity μ)) a) =
      (op.mapHead μ).2.reindex p (μ.sort a) := by
  cases op <;> simp only [childMap, mapHead, reindex, Scope.Map.sort,
    Scope.Map.liftNum, Scope.Map.liftType, Scope.Map.assume, Scheme.subst_subst, id_eq,
    ParameterSubstitution.weakenNum_comp_liftNum, ParameterSubstitution.weakenType_comp_liftType]

theorem childMap_binders {w z : Scope} (μ : Scope.Map w z) {s : w.ValueSort}
    (op : Op w s) (p : Fin (op.mapHead μ).2.arity) :
    (op.binders (p.cast (op.mapHead_arity μ))).map (op.childMap μ p).sort =
      (op.mapHead μ).2.binders p := by
  cases op <;> try rfl
  case letE value =>
    cases p using Fin.cases with
    | zero => rfl
    | succ p => rfl

theorem childMap_sort {w z : Scope} (μ : Scope.Map w z) {s : w.ValueSort}
    (op : Op w s) (p : Fin (op.mapHead μ).2.arity) :
    (op.childMap μ p).sort (op.sort (p.cast (op.mapHead_arity μ))) =
      (op.mapHead μ).2.sort p := by
  cases op <;> try first | rfl | exact Fin.elim0 p
  all_goals cases p using Fin.cases <;> try rfl
  rename_i bindings i
  change μ.sort (bindings[i.val]'(by simpa only [List.length_map] using i.isLt)) =
    (bindings.map μ.sort)[i.val]
  rw [List.getElem_map]

end Op

namespace Head

/-- Translate a checked head, keeping result equalities out of its child metadata. -/
@[expose] def map {w z : Scope} (μ : Scope.Map w z) {s : w.ValueSort} (h : Head w s) :
    Head z (μ.sort s) :=
  ⟨h.code.2.mapHead μ, (h.code.2.mapHead_result μ).trans (congrArg μ.sort h.result)⟩

end Head

/-- Constructor-local laws give the generic parameter traversal. -/
@[expose] def parameterHom :
    IPFunctor.ScopedFamily.Hom signature signature Scope.Map Scope.Map.sort where
  op := fun {_ _} μ {_} h => h.map μ
  arg := fun {_ _} μ {_} h p => p.cast (h.code.2.mapHead_arity μ)
  next := fun {_ _} μ {_} h p => h.code.2.childMap μ p
  binders := fun {_ _} μ {_} h p => h.code.2.childMap_binders μ p
  reindex := fun {_ _} μ {_} h p => h.code.2.childMap_reindex μ p
  sort := fun {_ _} μ {_} h p => h.code.2.childMap_sort μ p

/-- Capture-avoiding substitution of numeric and type parameters in a finite term. -/
@[expose] def Term.parameters {w z : Scope} (μ : Scope.Map w z)
    {Γ : List w.ValueSort} {s : w.ValueSort} (t : Term w Γ s) :
    Term z (Γ.map μ.sort) (μ.sort s) :=
  IPFunctor.ScopedFamily.Term.map parameterHom μ t

/-- Reindexing retains a variable's binding position, even if sorts merge. -/
@[simp] theorem Term.parameters_var {w z : Scope} (μ : Scope.Map w z)
    {Γ : List w.ValueSort} {s : w.ValueSort} (x : IPFunctor.ScopedVar Γ s) :
    Term.parameters μ (IPFunctor.ScopedFamily.Term.var x) =
      IPFunctor.ScopedFamily.Term.var (x.map μ.sort) := rfl

/-- Numeric and type substitution commutes with renaming local values. -/
theorem Term.parameters_rename {w z : Scope} (μ : Scope.Map w z)
    {Γ Δ : List w.ValueSort} {s : w.ValueSort}
    (ρ : IPFunctor.ScopedSignature.Renaming Γ Δ) (t : Term w Γ s) :
    Term.parameters μ (t.rename ρ) =
      (Term.parameters μ t).rename (IPFunctor.ScopedSignature.Renaming.map μ.sort ρ) :=
  IPFunctor.ScopedFamily.Term.map_rename parameterHom μ ρ t

end Interop.Cryptol.Polymorphic
