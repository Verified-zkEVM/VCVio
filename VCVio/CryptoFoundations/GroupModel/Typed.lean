/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.Interaction
public import VCVio.OracleComp.CanReturn
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Typed algebraic outputs over a fixed basis

Typed points retain both a value and its chosen coefficient vector; representations need not be
unique. Valid explanations and typed outputs are equivalent. At the program level the basis stays
fixed when every supported game reply has empty group lists. The bridge concerns executions in
that game, including their explained outputs and final basis, rather than constructing an adversary
certified against arbitrary replies. Plain reply data must not hide additional group inputs.
-/

public section

namespace GroupModel

open scoped BigOperators
open OracleComp OracleSpec

/-- A group element with a chosen representation over a finite basis. -/
@[ext]
structure AlgebraicPoint (F : Type) {G : Type} [AddCommMonoid G] [SMul F G]
    {ι : Type} [Fintype ι] (basis : ι → G) where
  point : G
  coeffs : ι → F
  eval_eq : ∑ i, coeffs i • basis i = point

namespace AlgebraicPoint

variable {F G ι : Type} [AddCommMonoid G] [SMul F G] [Fintype ι] {basis : ι → G}

/-- Compute a typed point from its coefficients. -/
@[expose] def ofCoeffs (basis : ι → G) (c : ι → F) : AlgebraicPoint F basis :=
  ⟨∑ i, c i • basis i, c, rfl⟩

@[simp] theorem ofCoeffs_coeffs (c : ι → F) : (ofCoeffs basis c).coeffs = c := rfl

@[simp] theorem ofCoeffs_point (c : ι → F) :
    (ofCoeffs basis c).point = ∑ i, c i • basis i := rfl

end AlgebraicPoint

namespace Interaction

/-- Exact-length vectors evaluate as the finite sum over the input basis. -/
theorem evaluate_ofFn {F G : Type} [Zero F] [AddCommMonoid G] [SMul F G]
    (xs : List G) (c : Fin xs.length → F) :
    evaluate (List.ofFn c) xs = ∑ i : Fin xs.length, c i • xs[i] := by
  simp [evaluate, List.mapIdx_eq_ofFn, List.sum_ofFn]

/-- A coefficient list of the basis length evaluates by its indexed coefficients. -/
theorem evaluate_eq_sum {F G : Type} [Zero F] [AddCommMonoid G] [SMul F G]
    (xs : List G) (cs : List F) (h : cs.length = xs.length) :
    evaluate cs xs = ∑ i : Fin xs.length, cs[i.val]'(by simpa only [h] using i.isLt) • xs[i] := by
  have he : List.ofFn (fun i : Fin xs.length => cs[i.val]'(by simpa only [h] using i.isLt)) = cs :=
    List.ext_getElem (by simp [h]) (by simp)
  simpa only [he] using evaluate_ofFn xs
    (fun i => cs[i.val]'(by simpa only [h] using i.isLt))

end Interaction

section Outputs

variable {F G : Type} [Zero F] [AddCommMonoid G] [SMul F G]

/-- Read aligned values and valid coefficient lists as typed points. -/
@[expose] def readPoints (xs : List G) (gs : List G) (cs : List (List F))
    (h : List.Forall₂ (fun g c => c.length = xs.length ∧ Interaction.evaluate c xs = g) gs cs) :
    List (AlgebraicPoint F (fun i : Fin xs.length => xs[i])) :=
  match gs, cs with
  | [], [] => []
  | [], _ :: _ => False.elim (by cases h)
  | _ :: _, [] => False.elim (by cases h)
  | g :: gs, c :: cs =>
    let hc := (List.forall₂_cons.mp h).1
    let ht := (List.forall₂_cons.mp h).2
    ⟨g, (fun i => c[i.val]'(by simpa only [hc.1] using i.isLt)),
      (Interaction.evaluate_eq_sum xs c hc.1).symm.trans hc.2⟩ :: readPoints xs gs cs ht

private theorem readPoints_points (xs : List G) (gs : List G) (cs : List (List F))
    (h : List.Forall₂ (fun g c => c.length = xs.length ∧ Interaction.evaluate c xs = g) gs cs) :
    (readPoints xs gs cs h).map AlgebraicPoint.point = gs := by
  induction h with
  | nil => rfl
  | cons h ht ih => exact congrArg (List.cons _) ih

private theorem readPoints_coeffs (xs : List G) (gs : List G) (cs : List (List F))
    (h : List.Forall₂ (fun g c => c.length = xs.length ∧ Interaction.evaluate c xs = g) gs cs) :
    (readPoints xs gs cs h).map (fun p => List.ofFn p.coeffs) = cs := by
  induction h with
  | nil => rfl
  | @cons g c gs cs h ht ih =>
    simp only [readPoints, List.map_cons, ih, List.cons.injEq, and_true]
    exact List.ext_getElem (by simp [h.1]) (by simp)

private theorem readPoints_vectors (xs : List G)
    (ps : List (AlgebraicPoint F (fun i : Fin xs.length => xs[i])))
    (h : List.Forall₂ (fun g c => c.length = xs.length ∧ Interaction.evaluate c xs = g)
      (ps.map fun p => Interaction.evaluate (List.ofFn p.coeffs) xs)
      (ps.map fun p => List.ofFn p.coeffs)) :
    readPoints xs _ _ h = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, readPoints, List.cons.injEq]
    constructor
    · apply AlgebraicPoint.ext
      · exact (Interaction.evaluate_ofFn xs p.coeffs).trans p.eval_eq
      · funext i
        simp
    · exact ih _

end Outputs

section SortedOutputs

variable {S F R : Type} {G : S → Type}
variable [Zero F] [∀ s, AddCommMonoid (G s)] [∀ s, SMul F (G s)]

/-- Plain result data and typed outputs, separately for every group sort. -/
abbrev TypedOutput (F R : Type) {S : Type} {G : S → Type}
    [∀ s, AddCommMonoid (G s)] [∀ s, SMul F (G s)] (inputs : Interaction.Groups G) :=
  R × ((s : S) → List (AlgebraicPoint F (fun i : Fin (inputs s).length => (inputs s)[i])))

/-- Valid explanations are exactly typed outputs, retaining each chosen representation. -/
@[expose] def explainedEquivTyped (inputs : Interaction.Groups G) :
    {out : Interaction.Explained F R G // out.Valid inputs} ≃ TypedOutput F R inputs where
  toFun out := ⟨out.val.value.data, fun s => readPoints (inputs s)
    (out.val.value.groups s) (out.val.coefficients s) (out.property s)⟩
  invFun out := ⟨Interaction.Explained.ofVectors inputs out.1
    (fun s => (out.2 s).map AlgebraicPoint.coeffs), Interaction.Explained.valid_ofVectors _ _ _⟩
  left_inv out := by
    apply Subtype.ext
    rcases out with ⟨⟨⟨data, gs⟩, cs⟩, h⟩
    dsimp
    have hp (s : S) :
        ((readPoints (inputs s) (gs s) (cs s) (h s)).map fun p =>
          Interaction.evaluate (List.ofFn p.coeffs) (inputs s)) = gs s := by
      simpa only [Interaction.evaluate_ofFn, AlgebraicPoint.eval_eq] using
        readPoints_points (inputs s) (gs s) (cs s) (h s)
    simp only [Interaction.Explained.ofVectors, List.map_map, Function.comp_def]
    congr 1
    · congr 1
      exact funext hp
    · exact funext fun s => readPoints_coeffs (inputs s) (gs s) (cs s) (h s)
  right_inv out := by
    rcases out with ⟨data, ps⟩
    apply Prod.ext
    · rfl
    funext s
    dsimp [Interaction.Explained.ofVectors]
    simp only [List.map_map, Function.comp_def]
    exact readPoints_vectors (inputs s) (ps s) _

end SortedOutputs

namespace Interaction

section Programs

variable {S F Input Query R I : Type} {G : S → Type}
variable {Reply : Query → Type} {ambient : OracleSpec I}
variable [Zero F] [∀ s, AddCommMonoid (G s)] [∀ s, SMul F (G s)]

/-- Every reachable reply of the game carries no additional group elements. This quantifies over
all plain requests, including requests outside a particular adversary's execution. -/
@[expose] def EmptyGroupReplies
    (impl : QueryImpl (plainSpec G Query Reply) (OracleComp ambient)) : Prop :=
  ∀ q reply, reply ∈ support (impl q) → reply.groups = fun _ => []

/-- Empty group replies preserve the entire chronological input basis. -/
theorem Adversary.run_basis
    (A : Adversary F G Input Query Reply R)
    (impl : QueryImpl (plainSpec G Query Reply) (OracleComp ambient))
    (hempty : EmptyGroupReplies impl) (input : Message Input G)
    (z : Explained F R G × Groups G) (hz : z ∈ support (A.run impl input)) :
    z.2 = input.groups := by
  unfold Adversary.run at hz
  generalize A.main input = program at hz
  generalize input.groups = basis at hz ⊢
  induction program using OracleComp.inductionOn generalizing basis z with
  | pure out =>
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        using congrArg Prod.snd hz
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk,
        bind_assoc, pure_bind] at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨reply, hr, hz⟩ := hz
      have he : extend basis reply.groups = basis := by
        rw [hempty q.value reply hr]
        funext s
        exact List.append_nil _
      exact (ih reply z _ hz).trans he

/-- Execute a certified adversary and attach its validity over the unchanged input basis. -/
@[expose] def Adversary.toTyped
    (A : Adversary F G Input Query Reply R)
    (impl : QueryImpl (plainSpec G Query Reply) (OracleComp ambient))
    (hempty : EmptyGroupReplies impl) (input : Message Input G) :
    OracleComp ambient (TypedOutput F R input.groups) :=
  (fun z => explainedEquivTyped input.groups ⟨z.val.1, by
    have hz := (canReturn_iff_mem_support _ _).mp z.property
    have hv := A.run_valid impl input z.val hz
    rwa [A.run_basis impl hempty input z.val hz] at hv⟩) <$>
      MonadAttach.attach (A.run impl input)

end Programs

end Interaction

section Forget

variable {S F R I : Type} {G : S → Type} {ambient : OracleSpec I}
variable [Zero F] [∀ s, AddCommMonoid (G s)] [∀ s, SMul F (G s)]

/-- Recover the explained output, including its coefficient lists, from typed points. -/
@[expose] def forget (inputs : Interaction.Groups G) (out : TypedOutput F R inputs) :
    Interaction.Explained F R G :=
  ((explainedEquivTyped inputs).symm out).val

/-- Interpret a typed-output computation as an explained execution with its fixed final basis. -/
@[expose] def ofTyped (inputs : Interaction.Groups G)
    (program : OracleComp ambient (TypedOutput F R inputs)) :
    OracleComp ambient (Interaction.Explained F R G × Interaction.Groups G) :=
  (fun out => (forget inputs out, inputs)) <$> program

/-- Recovering explanations from the typed execution preserves the original computation exactly. -/
theorem ofTyped_toTyped {Input Query : Type} {Reply : Query → Type}
    (A : Interaction.Adversary F G Input Query Reply R)
    (impl : QueryImpl (Interaction.plainSpec G Query Reply) (OracleComp ambient))
    (hempty : Interaction.EmptyGroupReplies impl) (input : Interaction.Message Input G) :
    ofTyped input.groups (A.toTyped impl hempty input) = A.run impl input := by
  unfold ofTyped Interaction.Adversary.toTyped
  rw [Functor.map_map]
  have he : (fun z : {z // MonadAttach.CanReturn (A.run impl input) z} =>
      (forget input.groups (explainedEquivTyped input.groups ⟨z.val.1, by
        have hz := (canReturn_iff_mem_support _ _).mp z.property
        have hv := A.run_valid impl input z.val hz
        rwa [A.run_basis impl hempty input z.val hz] at hv⟩), input.groups)) =
      Subtype.val := by
    funext z
    simp only [forget, Equiv.symm_apply_apply]
    exact Prod.ext rfl (A.run_basis impl hempty input z.val
      ((canReturn_iff_mem_support _ _).mp z.property)).symm
  change (fun z => _) <$> MonadAttach.attach (A.run impl input) = _
  rw [he]
  exact WeaklyLawfulMonadAttach.map_attach

end Forget

end GroupModel
