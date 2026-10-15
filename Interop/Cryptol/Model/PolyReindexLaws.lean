/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.PolyReindex
public import PolyFun.IPFunctor.Scoped.FamilyMapCongr
import Mathlib.Tactic.CongrExclamation

/-!
# Coherence of symbolic constructor substitution

Identity and composition retain constructor data, including recursive groups
and constraint evidence. Checked result annotations compare by heterogeneous
equality so clients need not choose a distinguished equality witness.
The child maps preserve identity and composition under numeric, type and proof
binders, so the same laws hold for complete finite terms.
-/

public section

namespace Interop.Cryptol.Polymorphic
namespace Op

/-- Equal word lengths give the same head, independent of constraint witnesses. -/
theorem wordLogic_heq {w : Scope} {l k : NumExpr w.numbers}
    (h : l = k) (op : BitOp) (hl : w.Entails (.fin l)) (hk : w.Entails (.fin k)) :
    HEq (Op.wordLogic l op hl) (Op.wordLogic k op hk) := by
  cases h
  rfl
/-- Identity parameter substitution preserves constructor data and its computed sort. -/
@[simp] theorem mapHead_id {w : Scope} {s : w.ValueSort} (op : Op w s) :
    op.mapHead (Scope.Map.id w) = ⟨s, op⟩ := by
  cases op <;> dsimp only [Op.mapHead, Scope.Map.id, Scope.Map.sort]
  case wordLogic l op h =>
    apply Sigma.ext
    · exact congrArg (fun k => Scheme.mono (.arrow (.seq k .bit)
        (.arrow (.seq k .bit) (.seq k .bit)))) (NumExpr.subst_id l)
    · exact wordLogic_heq (NumExpr.subst_id l) op _ _
  case letRec bs =>
    have hi : (Scope.Map.id w).sort = id := funext Scheme.subst_id
    change (⟨_, Op.letRec (bs.map (Scope.Map.id w).sort)
      ((Scope.Map.id w).sort s)⟩ : Sigma (Op w)) = _
    rw [hi, List.map_id]
    rfl
  all_goals congr! <;> try simp only [ParameterSubstitution.liftNum_id,
    ParameterSubstitution.liftType_id, ParameterSubstitution.apply_id,
    Scheme.subst_id]
  all_goals try simp only [ParameterSubstitution.id, NumExpr.subst_id, Constraint.subst_id]

/-- Successive substitutions of constructor data compose at all three binder kinds. -/
theorem mapHead_comp {w z u : Scope} (μ : Scope.Map w z) (ν : Scope.Map z u)
    {s : w.ValueSort} (op : Op w s) :
    (op.mapHead μ).2.mapHead ν = op.mapHead (μ.comp ν) := by
  apply Sigma.ext
  · simp only [Op.mapHead_result, Scope.Map.sort, Scheme.subst_subst]
    rfl
  · cases op <;> dsimp only [Op.mapHead, Scope.Map.comp, Scope.Map.sort]
    all_goals try exact wordLogic_heq (NumExpr.subst_subst _ _ _) _ _ _
    all_goals congr! 1 <;> try simp only [Scheme.subst_subst,
      ParameterSubstitution.apply_comp, ParameterSubstitution.liftNum_comp,
      ParameterSubstitution.liftType_comp]
    all_goals try simp only [ParameterSubstitution.comp, NumExpr.subst_subst,
      Constraint.subst_subst]
    all_goals try simp only [List.map_map, Scope.Map.sort,
      Scheme.subst_subst, Function.comp_def]
    all_goals try rfl

end Op
namespace Head

/-- A checked head is determined by its constructor data, across equal result sorts. -/
theorem heq_of_code_eq {w : Scope} {s t : w.ValueSort} {h : Head w s} {k : Head w t}
    (e : h.code = k.code) : HEq h k := by
  cases h with
  | mk hc he =>
    cases k with
    | mk kc ke =>
      cases e
      cases he
      cases ke
      rfl

/-- The identity retains a checked head, with no restriction on its result annotation. -/
@[simp] theorem map_id_heq {w : Scope} {s : w.ValueSort} (h : Head w s) :
    HEq (h.map (Scope.Map.id w)) h :=
  heq_of_code_eq (Op.mapHead_id h.code.2)

/-- Checked heads respect composition without exposing annotation transports. -/
theorem map_map_heq {w z u : Scope} (μ : Scope.Map w z) (ν : Scope.Map z u)
    {s : w.ValueSort} (h : Head w s) :
    HEq ((h.map μ).map ν) (h.map (μ.comp ν)) :=
  heq_of_code_eq (Op.mapHead_comp μ ν h.code.2)

end Head

namespace Op

/-- Identity substitution retains each child's parameter scope. -/
theorem childMap_id_world {w : Scope} {s : w.ValueSort} (op : Op w s)
    (p : Fin (op.mapHead (Scope.Map.id w)).2.arity) :
    (op.mapHead (Scope.Map.id w)).2.world p =
      op.world (p.cast (op.mapHead_arity (Scope.Map.id w))) := by
  cases op <;> simp only [mapHead, world, Scope.Map.id, ParameterSubstitution.id,
    Constraint.subst_id]

/-- Identity substitution lifts to the identity at every child. -/
theorem childMap_id_heq {w : Scope} {s : w.ValueSort} (op : Op w s)
    (p : Fin (op.mapHead (Scope.Map.id w)).2.arity) :
    HEq (op.childMap (Scope.Map.id w) p)
      (Scope.Map.id (op.world (p.cast (op.mapHead_arity (Scope.Map.id w))))) := by
  apply Scope.Map.heq_of_parameters_heq _ _ (op.childMap_id_world p)
  cases op <;> simp only [childMap, Scope.Map.liftNum, Scope.Map.liftType, Scope.Map.assume,
    Scope.Map.id, ParameterSubstitution.liftNum_id, ParameterSubstitution.liftType_id]
  all_goals rfl

end Op

/-- Parameter identity retains the complete term, including transported annotations. -/
@[simp] theorem Term.parameters_id_heq {w : Scope} {Γ : List w.ValueSort} {s : w.ValueSort}
    (t : Term w Γ s) : HEq (Term.parameters (Scope.Map.id w) t) t := by
  apply HEq.trans ?_ (IPFunctor.ScopedFamily.Term.map_identity_heq ⟨rfl⟩ t)
  apply IPFunctor.ScopedFamily.Term.map_congr parameterHom
    (IPFunctor.ScopedFamily.Hom.identity signature)
    (fun {a b _} μ _ => b = a ∧ HEq μ (Scope.Map.id a)) ?_ ?_ ?_ ?_ ?_
    (show w = w ∧ HEq (Scope.Map.id w) (Scope.Map.id w) from ⟨rfl, HEq.rfl⟩) t
  · intro a b c μ ν hr
    exact hr.1.trans ν.down
  · intro a b c μ ν hr
    rcases hr with ⟨hb, hμ⟩
    cases hb
    cases eq_of_heq hμ
    cases ν.down
    exact heq_of_eq (funext Scheme.subst_id)
  · intro a b c μ ν hr s op
    rcases hr with ⟨hb, hμ⟩
    cases hb
    cases eq_of_heq hμ
    cases ν.down
    exact Head.map_id_heq op
  · intro a b c μ ν hr s op p q he
    rcases hr with ⟨hb, hμ⟩
    cases hb
    cases eq_of_heq hμ
    cases ν.down
    apply Fin.ext
    change p.val = q.val
    exact Fin.val_eq_val_of_heq he
  · intro a b c μ ν hr s op p q he
    rcases hr with ⟨hb, hμ⟩
    cases hb
    cases eq_of_heq hμ
    cases ν.down
    exact ⟨op.code.2.childMap_id_world p, op.code.2.childMap_id_heq p⟩

/-- Successive parameter substitutions compose throughout a finite term. -/
theorem Term.parameters_parameters_heq {w z u : Scope} (μ : Scope.Map w z)
    (ν : Scope.Map z u) {Γ : List w.ValueSort} {s : w.ValueSort} (t : Term w Γ s) :
    HEq (Term.parameters ν (Term.parameters μ t)) (Term.parameters (μ.comp ν) t) := by
  have hm := IPFunctor.ScopedFamily.Term.map_map parameterHom parameterHom μ ν t
  apply (IPFunctor.ScopedFamily.Term.cast_heq _ _ _).symm.trans
  apply (heq_of_eq hm).trans
  apply IPFunctor.ScopedFamily.Term.map_congr (parameterHom.comp parameterHom) parameterHom
    (fun {a b c} μ ν => b = c ∧ HEq (μ.2.1.comp μ.2.2) ν)
    ?_ ?_ ?_ ?_ ?_ ⟨rfl, HEq.rfl⟩ t
  · intro a b c μ ν hr
    exact hr.1
  · intro a b c μ ν hr
    rcases hr with ⟨hb, hμ⟩
    cases hb
    cases eq_of_heq hμ
    exact heq_of_eq (funext (fun s => Scheme.subst_subst s μ.2.1.parameters μ.2.2.parameters))
  · intro a b c μ ν hr s op
    rcases hr with ⟨hb, hμ⟩
    cases hb
    cases eq_of_heq hμ
    exact Head.map_map_heq μ.2.1 μ.2.2 op
  · intro a b c μ ν hr s op p q he
    rcases hr with ⟨hb, hμ⟩
    cases hb
    cases eq_of_heq hμ
    apply Fin.ext
    change p.val = q.val
    exact Fin.val_eq_val_of_heq he
  · intro a b c μ ν hr s op p q he
    rcases hr with ⟨hb, hμ⟩
    cases hb
    cases eq_of_heq hμ
    rcases μ with ⟨mid, μ, ν⟩
    cases op with
    | mk code annotation =>
      cases code with
      | mk sort op =>
        cases annotation
        refine ⟨?_, ?_⟩
        · change ((op.mapHead μ).2.mapHead ν).2.world p = (op.mapHead (μ.comp ν)).2.world q
          have hw (x y : Sigma (Op b)) (hxy : x = y)
              (p : Fin x.2.arity) (q : Fin y.2.arity) : x.2.world p = y.2.world q := by
            cases hxy
            cases x with
            | mk a x => cases x <;> rfl
          exact hw _ _ (op.mapHead_comp μ ν) p q
        · simp only [heq_eqRec_iff]
          change HEq ((op.childMap μ (p.cast ((op.mapHead μ).2.mapHead_arity ν))).comp
            ((op.mapHead μ).2.childMap ν p)) (op.childMap (μ.comp ν) q)
          cases op <;> dsimp only [Op.childMap, Op.mapHead]
          all_goals try exact HEq.rfl
          · exact heq_of_eq (Scope.Map.liftNum_comp μ ν).symm
          · exact heq_of_eq (Scope.Map.liftType_comp μ ν).symm
          · exact Scope.Map.assume_comp_heq μ ν _

end Interop.Cryptol.Polymorphic
